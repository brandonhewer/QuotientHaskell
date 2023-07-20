{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TupleSections         #-}

{- Module for handling quotient type checks during constraint generation

   Includes implementation of normalisation by evaluation with built-in
   rewriting via quotients.

   TODO:
     * Consider improving the type propagation built into the NBE procedure
       so that quotient rewriting can be applied more generally. At present
       quotient rewrite rules cannot be applied to terms of a quotient type
       that appear as direct descendants of an equality expression node.
       This issue arises because very little type information propagates up
       from the leaves of an expression in the NBE procedure, and instead we
       'break apart' an initial type.
-}
module Language.Haskell.Liquid.Constraint.Quotient
  ( performQuotientChecks
  ) where

import           Control.Applicative                      ((<|>))
import           Control.Monad.Extra                      (anyM, allM, whenJust)
import           Control.Monad.Reader                     (MonadReader)
import qualified Control.Monad.Reader                     as RD
import           Control.Monad.State.Strict               (MonadState)
import qualified Control.Monad.State.Strict               as ST

import           Data.Bifunctor                           (first)
import qualified Data.Default                             as Default
import qualified Data.Foldable                            as Fold
import qualified Data.Foldable.Extra                      as Fold
import qualified Data.List                                as L
import           Data.Hashable                            (Hashable)
import qualified Data.Hashable                            as Hash
import           Data.HashMap.Strict                      (HashMap)
import qualified Data.HashMap.Strict                      as M
import           Data.HashSet                             (HashSet)
import qualified Data.HashSet                             as S
import qualified Data.Maybe                               as MB
import qualified Data.Text                                as Text
import qualified Data.Text.Encoding                       as Text

import qualified Language.Fixpoint.Solver.Simplify        as F
import           Language.Fixpoint.Types                  (Brel, Constant, Equation, Expr, QPattern, Symbol)
import qualified Language.Fixpoint.Types                  as F
import qualified Language.Haskell.Liquid.Bare.DataType    as Bare
import qualified Language.Haskell.Liquid.Constraint.Env   as CG
import qualified Language.Haskell.Liquid.Constraint.Monad as CG
import           Language.Haskell.Liquid.Constraint.Types (CG, CGEnv, QuotientRewrite)
import qualified Language.Haskell.Liquid.Constraint.Types as CG
import           Language.Haskell.Liquid.Types            (LocSpecType, SpecQuotient, SpecQuotientType, SpecType)
import qualified Language.Haskell.Liquid.Types            as LH

import           Liquid.GHC.API                           (AltCon, CoreAlt, CoreExpr, CoreBndr, Var)
import qualified Liquid.GHC.API                           as GHC

import           Language.Haskell.Liquid.Constraint.ToFixpoint  (makeSimplify)
import qualified Language.Haskell.Liquid.Transforms.CoreToLogic as CL

import Debug.Trace (trace)

data AppNormaliser m
  = AppNormaliser
      { argumentTypes  :: [SpecType]
      , doNormaliseApp :: [Expr] -> m (NBEResult Expr)
      }

-- | The result of rewriting, with a possible precondition that must hold for this
--   rewrite result to be applicable.
data RewriteResult a
  = RWResult
      { rwCondition   :: !(Maybe Expr)
      -- | ^ The precondition that must hold before this rewrite is applicable
      , rwResult      :: !a
      -- | ^ The rewritten expression
      , rwQuantifiers :: !(HashSet Symbol)
      -- | ^ The free variables in rwResult/rwCondition that should be quantified over
      } deriving Functor

-- | Typed definitions in the environment
data NBEDefinition
  = NBEDefinition
      { nbeUnfoldTotal :: !Int      -- | How many times this definition has been unfolded
      , nbeType        :: !SpecType -- | Type of the definition
      , nbeDefinition  :: !Expr     -- | Body of the definition
      }

-- | Environment for normalisation by evaluation
data NBEEnv
  = NBE
      { nbeDefs      :: !(HashMap Symbol NBEDefinition)
        -- | ^ Definitions that can be unfolded
      , nbeSelectors :: !(HashMap Symbol (Symbol, Int))
        -- | ^ Selectors such that a selector symbol maps to its data constructor
        --     and projection index.
      , nbeDataCons  :: !(HashMap Symbol SpecType)
        -- | ^ Reflected data constructors.
      , nbeGuards    :: ![Expr]
        -- | ^ List of (normalised) axioms.
      , nbeRewrites  :: !(M.HashMap F.Symbol [QuotientRewrite])
        -- | ^ List of rewrite rules that can be applied, map from Quotient TyCon.
      }

data BinderType
  = KnownType SpecType
  | UnknownType

newtype NBEState
  = NBEState
      { nbeBinds :: HashMap Symbol BinderType
        -- | ^ The bindings in scope (cannot be unfolded) with possibly discovered types.
        --     Act as free variables in open terms for the purpose of rewriting.
      } 

newtype NBEResult a
  = NBEResult [RewriteResult a]
    deriving (Foldable, Functor, Traversable)

-----------------------------------------------------------------------
--  Instances
-----------------------------------------------------------------------

instance Eq a => Eq (RewriteResult a) where
  r1 == r2
    =  rwCondition r1 == rwCondition r2
    && rwResult    r1 == rwResult r2

instance Hashable a => Hashable (RewriteResult a) where
  hashWithSalt n RWResult {..}
    = Hash.hashWithSalt (Hash.hashWithSalt n rwCondition) rwResult

instance Semigroup (NBEResult a) where
  NBEResult as <> NBEResult bs = NBEResult (as <> bs)

instance Monoid (NBEResult a) where
  mempty = NBEResult []

instance Foldable RewriteResult where
  foldr f z RWResult { rwResult } = f rwResult z

instance Traversable RewriteResult where
  traverse f RWResult {..} = g <$> f rwResult
    where
      g b
        = RWResult
            { rwCondition
            , rwQuantifiers
            , rwResult = b
            }

-----------------------------------------------------------------------
-- Utility functions
-----------------------------------------------------------------------

foldMapM :: (Monoid b, Monad m, Foldable f) => (a -> m b) -> f a -> m b
foldMapM f xs = foldr step return xs mempty
  where
    step x r z = f x >>= \y -> r $! z `mappend` y

pureRW :: a -> RewriteResult a
pureRW result
  = RWResult
      { rwCondition   = Nothing
      , rwResult      = result
      , rwQuantifiers = mempty
      }

pureResult :: a -> NBEResult a
pureResult a = NBEResult [pureRW a]

getAppArgs :: Expr -> Expr -> (Expr, [Expr])
getAppArgs f a = go [a] f
  where
    go acc (F.EApp g e) = go (e:acc) g
    go acc e            = (e, acc)    

getLamBinds :: Expr -> [Expr] -> (HashMap Symbol Expr, Expr)
getLamBinds = go mempty
  where
    go :: HashMap Symbol Expr -> Expr -> [Expr] -> (HashMap Symbol Expr, Expr)
    go bs b                 []       = (bs, b)
    go bs (F.ELam (s, _) b) (a : as) = go (M.insert s a bs) b as
    go bs e                 as       = (bs, Fold.foldl' F.EApp e as)

zipWithThenMap :: (a -> b -> c) -> (b -> c) -> [a] -> [b] -> [c]
zipWithThenMap _ _ []       []       = []
zipWithThenMap _ _ _        []       = []
zipWithThenMap _ g []       bs       = map g bs
zipWithThenMap f g (a : as) (b : bs) = f a b : zipWithThenMap f g as bs

extend :: [a] -> [a] -> [a]
extend []       xs       = xs
extend xs       []       = xs
extend (x : xs) (_ : ys) = x : extend xs ys

safeTail :: [a] -> [a]
safeTail []       = []
safeTail (_ : as) = as

boolType :: SpecType
boolType = LH.RApp (LH.RTyCon GHC.boolTyCon [] Default.def) [] [] mempty

-----------------------------------------------------------------------
--  Normalisation by evaluation
-----------------------------------------------------------------------

mergeAnd :: Expr -> Expr -> Expr
mergeAnd (F.PAnd ps) (F.PAnd qs) = F.PAnd (ps ++ qs)
mergeAnd (F.PAnd ps) p           = F.PAnd (p : ps)
mergeAnd p           (F.PAnd ps) = F.PAnd (p : ps)
mergeAnd p           q           = F.PAnd [p, q]

mergeOr :: Expr -> Expr -> Expr
mergeOr (F.POr ps) (F.POr qs) = F.POr (ps ++ qs)
mergeOr (F.POr ps) p          = F.POr (p : ps)
mergeOr p          (F.POr ps) = F.POr (p : ps)
mergeOr p          q          = F.POr [p, q]

splitAnd :: Expr -> [Expr]
splitAnd (F.PAnd ps) = concatMap splitAnd ps
splitAnd e           = [e]

-- | IMPROVE: This can do further evaluation
implies :: Expr -> Expr -> Bool
implies F.PFalse               _             = True
implies np@(F.PNot (F.PNot p)) q             = np == q || p `implies` q
implies p                      q@(F.PAnd qs) = p == q  || Fold.all (p `implies`) qs
implies p                      q@(F.POr qs)  = p == q  || Fold.any (p `implies`) qs
implies p@(F.PAnd ps)          q             = p == q  || Fold.any (`implies` q) ps
implies p@(F.POr ps)           q             = p == q  || Fold.all (`implies` q) ps
implies p                      q             = p == q

-- | Check whether a predicate is true in a given NBE environment
--   Returns Just b if there is a known truth value or Nothing otherwise
guardTruth :: MonadReader NBEEnv m => Expr -> m (Maybe Bool)
guardTruth F.PTrue  = return $ Just True
guardTruth F.PFalse = return $ Just False
guardTruth e        = RD.asks $ computeTruth e . nbeGuards
  where
    computeTruth :: Expr -> [Expr] -> Maybe Bool
    computeTruth (F.PAnd es) guards
      = allM (`computeTruth` guards) es
    computeTruth p@(F.POr es) guards
      | Fold.any (`implies` p) guards = Just True
      | otherwise                     = anyM (`computeTruth` guards) es
    computeTruth p@(F.PNot e) guards
      | Fold.any (`implies` p) guards = Just True
      | otherwise                     = not <$> computeTruth e guards
    computeTruth p@(F.PImp c b) guards
      | Fold.any (`implies` p) guards = Just True
      | otherwise
          = case computeTruth c guards of
              Just True  -> computeTruth b guards
              Just False -> Just True
              Nothing    ->
                case computeTruth b guards of
                  Just True -> Just True
                  _         -> Nothing
    computeTruth p@(F.PIff l r) guards
      | Fold.any (`implies` p) guards = Just True
      | otherwise
          = case (computeTruth l guards, computeTruth r guards) of
              (Just True  , Just True)  -> Just True
              (Just False , Just False) -> Just True
              (Just _     , Just _)     -> Just False
              _                         -> Nothing
    computeTruth p@(F.EIte c i e) guards
      | Fold.any (`implies` p) guards = Just True
      | otherwise
          = case computeTruth c guards of
              Just True  -> computeTruth i guards
              Just False -> computeTruth e guards
              Nothing    ->
                case (computeTruth i guards, computeTruth e guards) of
                  (Just True  , Just True)  -> Just True
                  (Just False , Just False) -> Just False
                  _                         -> Nothing
    computeTruth p guards
      | Fold.any (`implies` p)        guards = Just True
      | Fold.any (`implies` F.PNot p) guards = Just False
      | otherwise                            = Nothing

applyRewrites :: MonadReader NBEEnv m => Maybe SpecType -> ([QuotientRewrite] -> a) -> m a
applyRewrites (Just (LH.RApp (LH.QTyCon nm _ _ _ _ _) _ _ _)) f
  = RD.asks (f . MB.fromMaybe [] . M.lookup (F.symbol nm) . nbeRewrites)
applyRewrites (Just t) f
  = let rep = LH.toRTypeRep t
     in case LH.ty_res rep of
          LH.RApp (LH.QTyCon nm _ _ _ _ _) _ _ _
            | null (LH.ty_args rep) ->
                RD.asks (f . MB.fromMaybe [] . M.lookup (F.symbol nm) . nbeRewrites)
            | otherwise -> return $ f []
          _ -> return $ f []
applyRewrites Nothing f = return $ f []

-- | Removes preconditions when they are satisfied by guards in the environment
simplifyResult :: MonadReader NBEEnv m => NBEResult a -> m (NBEResult a)
simplifyResult (NBEResult [])                     = return $ NBEResult []
simplifyResult (NBEResult (r@RWResult {..} : rs)) = do
  NBEResult srs <- simplifyResult $ NBEResult rs
  Fold.firstJustM guardTruth rwCondition >>= \case
      Just True  -> return $ NBEResult (r { rwCondition = Nothing } : srs)
      Just False -> return $ NBEResult srs
      Nothing    -> return $ NBEResult (r : srs)

makeRewriteResult
  :: MonadReader NBEEnv m
  => Maybe SpecType
  -> ([QuotientRewrite] -> NBEResult a)
  -> m (NBEResult a)
makeRewriteResult t f = applyRewrites t f >>= simplifyResult

updateBindType :: MonadState NBEState m => Symbol -> SpecType -> m ()
updateBindType sym t = do
  s@NBEState { nbeBinds } <- ST.get
  ST.put s { nbeBinds = M.alter doUpdate sym nbeBinds }
  where
    doUpdate :: Maybe BinderType -> Maybe BinderType
    doUpdate Nothing              = Just (KnownType t)
    doUpdate (Just UnknownType)   = Just (KnownType t)
    doUpdate (Just (KnownType _)) = Just (KnownType t)
    -- ^ IMPROVE THIS: Should be a better way to choose which type to maintain
    --                 i.e. the more informative one with respect to quotient types

addGuard :: Expr -> NBEEnv -> NBEEnv
addGuard e env@NBE { nbeGuards }
  = env { nbeGuards = splitAnd e ++ nbeGuards }

withGuard :: MonadReader NBEEnv m => Expr -> m a -> m a
withGuard = RD.local . addGuard

getDefinition :: MonadReader NBEEnv m => Symbol -> m (Maybe NBEDefinition)
getDefinition sym = RD.asks (M.lookup sym . nbeDefs)

incrementUnfold :: Symbol -> NBEEnv -> NBEEnv
incrementUnfold sym env@NBE { nbeDefs }
  = env { nbeDefs = M.adjust updateCount sym nbeDefs }
    where
      updateCount :: NBEDefinition -> NBEDefinition
      updateCount def@NBEDefinition { nbeUnfoldTotal }
        = def { nbeUnfoldTotal = 1 + nbeUnfoldTotal }

unfoldDefinitionIn :: MonadReader NBEEnv m => Symbol -> m a -> m a
unfoldDefinitionIn sym = RD.local (incrementUnfold sym)

getFreeVariables :: MonadState NBEState m  => m (HashSet Symbol)
getFreeVariables = ST.gets (M.keysSet . nbeBinds)

getBinder :: MonadState NBEState m => Symbol -> m (Maybe BinderType)
getBinder sym = ST.gets (M.lookup sym . nbeBinds)

withBinder :: MonadState NBEState m => Symbol -> m a -> m a
withBinder sym ma = do
  st@NBEState { nbeBinds } <- ST.get
  ST.put st { nbeBinds = M.alter (const $ Just UnknownType) sym nbeBinds }
  result <- ma
  ST.put st { nbeBinds = nbeBinds }
  return result

isDataCons :: MonadReader NBEEnv m => Symbol -> m Bool
isDataCons sym = RD.asks (M.member sym . nbeDataCons)

getDataConsType :: MonadReader NBEEnv m => Symbol -> m (Maybe SpecType)
getDataConsType sym = RD.asks (M.lookup sym . nbeDataCons)

getSelector :: MonadReader NBEEnv m => Symbol -> m (Maybe (Symbol, Int))
getSelector sym = RD.asks (M.lookup sym . nbeSelectors)

addQuantifiers
  :: HashSet Symbol
  -> RewriteResult a
  -> RewriteResult a
addQuantifiers qs r@RWResult {..} = r { rwQuantifiers = S.union qs rwQuantifiers }

addCondition :: Expr -> RewriteResult a -> RewriteResult a
addCondition pc r@RWResult {..}
  = case rwCondition of
      Nothing -> r { rwCondition = Just pc }
      Just c  -> r { rwCondition = Just (mergeAnd pc c) }

forEachResult
  :: MonadReader NBEEnv m
  => NBEResult a
  -> (a -> m (NBEResult b))
  -> m (NBEResult b)
forEachResult (NBEResult rs) f
  = foldMapM
      (\RWResult {..} ->
          case rwCondition of
            Nothing -> do
              NBEResult rrs <- f rwResult
              return $ NBEResult $ map (addQuantifiers rwQuantifiers) rrs
            Just cd -> guardTruth cd >>= \case
              Just True  -> do
                NBEResult rrs <- f rwResult
                return $ NBEResult $ map (addQuantifiers rwQuantifiers) rrs
              Just False -> return mempty
              Nothing    -> do
                NBEResult rrs <- f rwResult
                return $ NBEResult $ map (addQuantifiers rwQuantifiers . addCondition cd) rrs
      ) rs

forEachResult2
  :: MonadReader NBEEnv m
  => NBEResult a
  -> NBEResult b
  -> (a -> b -> m (NBEResult c))
  -> m (NBEResult c)
forEachResult2 x y f = forEachResult x (forEachResult y . f)

forEachPure :: MonadReader NBEEnv m => NBEResult a -> (a -> b) -> m (NBEResult b)
forEachPure r f = forEachResult r (return . pureResult . f)

forEachPure2
  :: MonadReader NBEEnv m
  => NBEResult a
  -> NBEResult b
  -> (a -> b -> c)
  -> m (NBEResult c)
forEachPure2 x y f
  = forEachResult2 x y
      $ \a b -> return $ pureResult $ f a b

forAllResults
  :: MonadReader NBEEnv m
  => [NBEResult a]
  -> ([a] -> m (NBEResult c))
  -> m (NBEResult c)
forAllResults []       f = f []
forAllResults (r : rs) f
  = forEachResult r $ \a ->
      forAllResults rs $ \as -> f (a : as)

checkGuard
  :: MonadReader NBEEnv m
  => NBEResult Expr
  -> (Either Expr Bool -> m (NBEResult a))
  -> m (NBEResult a)
checkGuard rp f
  = forEachResult rp $ \p -> guardTruth p >>= \case
      Nothing -> f (Left p)
      Just b  -> f (Right b)

checkGuardPure
  :: MonadReader NBEEnv m
  => NBEResult Expr
  -> (Either Expr Bool -> a)
  -> m (NBEResult a)
checkGuardPure rp f = checkGuard rp (return . pureResult . f)

checkGuardPure2
  :: MonadReader NBEEnv m
  => NBEResult Expr
  -> NBEResult Expr
  -> ((Either Expr Bool, Either Expr Bool) -> a)
  -> m (NBEResult a)
checkGuardPure2 x y f
  = checkGuard x $ \ex -> checkGuardPure y $ \ey -> f (ex, ey)

normalise
  :: (MonadReader NBEEnv m, MonadState NBEState m)
  => Maybe SpecType
  -- | ^ Approximate type of the below expression
  --     Accurate enough to know whether we have applicable quotients
  -> Expr
  -> m (NBEResult Expr)
normalise u (F.ECst e t) = (flip F.ECst t <$>) <$> normalise u e
normalise _ (F.ESym s)   = return $ pureResult $ F.ESym s
normalise t (F.ECon c)   = makeRewriteResult t (litRewrites c)
normalise t (F.EVar v)
  = getDefinition v >>= \case
      Nothing       -> getBinder v >>= \case
        Nothing            -> return $ pureResult $ F.EVar v
        Just (KnownType u) -> makeRewriteResult (Just u) (varRewrites v)
        Just UnknownType   -> do
          whenJust t $ updateBindType v
          makeRewriteResult t (varRewrites v)
      Just d -> normaliseDefinition v d
normalise t (F.EApp ie ia) = normaliseApp t ie ia
normalise t (F.ENeg e) = do
  ne <- normalise t e
  forEachPure ne normaliseNeg
normalise t (F.EBin op x y) = do
  nx <- normalise t x
  ny <- normalise t y
  forEachPure2 nx ny (F.applyConstantFolding op)
normalise t (F.EIte p ib eb) = normaliseITE t p ib eb
normalise t (F.ELam (s, _) b) = normaliseLam t s b
normalise t (F.ETApp e u) = do
  ne <- normalise t e
  forEachPure ne (`F.ETApp` u)
normalise t (F.ETAbs e s) = do
  ne <- normalise t e
  forEachPure ne (`F.ETAbs` s)
normalise t (F.PAnd ps) = normaliseAnd (MB.fromMaybe boolType t) ps
normalise t (F.POr ps) = normaliseOr (MB.fromMaybe boolType t) ps
normalise t (F.PNot e) = do
  ne <- normalise (t <|> Just boolType) e
  checkGuardPure ne $ \case
    Right True  -> F.PFalse
    Right False -> F.PTrue
    Left  e     -> normaliseNot e
normalise t (F.PImp i a) = normaliseImp (t <|> Just boolType) i a
normalise t (F.PIff l r) = normaliseIff (t <|> Just boolType) l r
normalise t (F.PAtom r x y) = do
  let u = if canPropagateRelType r then t else Nothing
  nx <- normalise u x
  ny <- normalise u y
  forEachPure2 nx ny $ F.applyBooleanFolding r
normalise _ e@(F.PKVar _ _) = return $ pureResult e
normalise t (F.PAll [] e) = normalise t e
normalise _ e@(F.PAll _ _) = return $ pureResult e
normalise t (F.PExist [] e) = normalise t e
normalise _ e@(F.PExist _ _) = return $ pureResult e
normalise _ e@(F.PGrad {}) = return $ pureResult e
normalise t (F.ECoerc x y e)
  | x == y    = normalise t e
  | otherwise = do
      ne <- normalise t e
      forEachPure ne (F.ECoerc x y)

normaliseDefinition
  :: (MonadReader NBEEnv m, MonadState NBEState m)
  => Symbol
  -> NBEDefinition
  -> m (NBEResult Expr)
normaliseDefinition name NBEDefinition {..}
  | nbeUnfoldTotal < 5 = unfoldDefinitionIn name $ normalise (Just nbeType) nbeDefinition
  | otherwise          = return $ pureResult $ F.EVar name

normaliseApp
  :: (MonadReader NBEEnv m, MonadState NBEState m)
  => Maybe SpecType
  -> Expr
  -> Expr
  -> m (NBEResult Expr)
normaliseApp t ie ia = do
  nf <- normalise Nothing f'

  forEachResult nf $ \f -> do
    an <- getAppNormaliser t f
    runAppNormaliser an as'
  where
    (f', as') = getAppArgs ie ia

runAppNormaliser
  :: (MonadReader NBEEnv m, MonadState NBEState m)
  => AppNormaliser m
  -> [Expr]
  -> m (NBEResult Expr)
runAppNormaliser AppNormaliser {..} as
  | null argumentTypes = do
      nas <- traverse (normalise Nothing) as
      forAllResults nas doNormaliseApp
  | otherwise          = do
      let addTy ty a = (Just ty, a)
          tyArgs     = zipWithThenMap addTy (Nothing,) argumentTypes as
      nas <- traverse (uncurry normalise) tyArgs
      forAllResults nas doNormaliseApp

getAppNormaliser
  :: (MonadReader NBEEnv m, MonadState NBEState m)
  => Maybe SpecType
  -> Expr
  -> m (AppNormaliser m)
getAppNormaliser t (F.EVar v) = getDefinition v >>= \case
  Just NBEDefinition {nbeType} -> do
    let types = LH.ty_args $ LH.toRTypeRep nbeType
    return AppNormaliser
      { argumentTypes  = types
      , doNormaliseApp = return . pureResult . Fold.foldl' F.EApp (F.EVar v)
      }
  Nothing -> getDataConsType v >>= \case
    Just u  ->
      return AppNormaliser
        { argumentTypes  = resolveJoins t $ LH.ty_args $ LH.toRTypeRep u
        , doNormaliseApp = normaliseDataConApp t v
        }
    Nothing -> getBinder v >>= \case
      Just (KnownType ft) -> do
        let types = LH.ty_args $ LH.toRTypeRep ft
        return AppNormaliser
          { argumentTypes  = types
          , doNormaliseApp = normaliseVarApp v
          }
      _ ->
        return AppNormaliser
          { argumentTypes  = []
          , doNormaliseApp = normaliseVarApp v
          }
getAppNormaliser t (F.EIte p ib eb) = do
  ian <- getAppNormaliser t ib
  ean <- getAppNormaliser t eb
  let types = extend (argumentTypes ian) (argumentTypes ean)
  return AppNormaliser
    { argumentTypes  = types
    , doNormaliseApp = \as -> do
        nib <- runAppNormaliser (ian { argumentTypes = types }) as
        neb <- runAppNormaliser (ean { argumentTypes = types }) as
        forEachPure2 nib neb (F.EIte p)
    }
getAppNormaliser t f 
  = return AppNormaliser
      { argumentTypes  = []
      , doNormaliseApp = \as -> do
          let (binds, body) = getLamBinds f as
          if M.null binds then
            return $ pureResult body
          else
            normalise t $ F.subst (F.Su binds) body
      }

normaliseDataConApp
  :: (MonadReader NBEEnv m, MonadState NBEState m)
  => Maybe SpecType
  -> Symbol
  -> [Expr]
  -> m (NBEResult Expr)
normaliseDataConApp t c as = do
  fvs <- getFreeVariables
  let app = Fold.foldl' F.EApp (F.EVar c) as
  makeRewriteResult t (conRewrites fvs app c as)

normaliseVarApp
  :: (MonadReader NBEEnv m, MonadState NBEState m)
  => Symbol
  -> [Expr]
  -> m (NBEResult Expr)
normaliseVarApp v as
  | F.isTestSymbol v = case as of
      [c] -> pureResult <$> normaliseTest v c
      _   -> return $ pureResult $ Fold.foldl' F.EApp (F.EVar v) as
  | otherwise = getSelector v >>= \case
      Just sel -> case as of
        [r] -> return $ pureResult $ normaliseSelector v sel r
        _   -> return $ pureResult $ Fold.foldl' F.EApp (F.EVar v) as
      Nothing -> return $ pureResult $ Fold.foldl' F.EApp (F.EVar v) as

normaliseLam
  :: (MonadReader NBEEnv m, MonadState NBEState m)
  => Maybe SpecType
  -> Symbol
  -> Expr
  -> m (NBEResult Expr)
normaliseLam t s b
  = withBinder s $ case t of
      Nothing -> normalise Nothing b
      Just u  -> do
        let ur = LH.toRTypeRep u
            nt = LH.fromRTypeRep ur
                  { LH.ty_binds = safeTail $ LH.ty_binds ur
                  , LH.ty_info  = safeTail $ LH.ty_info  ur
                  , LH.ty_args  = safeTail $ LH.ty_args  ur
                  , LH.ty_refts = safeTail $ LH.ty_refts ur
                  }
        normalise (Just nt) b

normaliseAnd
  :: (MonadReader NBEEnv m, MonadState NBEState m)
  => SpecType
  -> [Expr]
  -> m (NBEResult Expr)
normaliseAnd t ps = do
  rps <- reduceAnd [] ps
  forEachPure rps $ \case
    Right True  -> F.PTrue
    Right False -> F.PFalse
    Left  es    -> F.PAnd es
  where
    reduceAnd [] [] = return $ pureResult $ Right True
    reduceAnd qs [] = return $ pureResult $ Left qs
    reduceAnd qs (p : ps) = do
      np  <- normalise (Just t) p
      checkGuard np $ \case
        Right True  -> reduceAnd qs ps
        Right False -> return $ pureResult $ Right False
        Left  e     -> reduceAnd (e : qs) ps

normaliseOr
  :: (MonadReader NBEEnv m, MonadState NBEState m)
  => SpecType
  -> [Expr]
  -> m (NBEResult Expr)
normaliseOr t ps = do
  rps <- reduceOr [] ps
  forEachPure rps $ \case
    Right True  -> F.PTrue
    Right False -> F.PFalse
    Left  es    -> F.POr es
  where
    reduceOr [] [] = return $ pureResult $ Right False
    reduceOr qs [] = return $ pureResult $ Left qs
    reduceOr qs (p : ps) = do
      np  <- normalise (Just t) p
      checkGuard np $ \case
        Right True  -> return $ pureResult $ Right True
        Right False -> reduceOr qs ps
        Left  e     -> reduceOr (e : qs) ps

normaliseImp
  :: (MonadReader NBEEnv m, MonadState NBEState m)
  => Maybe SpecType
  -> Expr
  -> Expr
  -> m (NBEResult Expr)
normaliseImp t i a = do
  ni <- normalise t i
  checkGuard ni $ \case
    Right False -> return $ pureResult F.PTrue
    Right True  -> do
      na <- normalise t a
      checkGuardPure na $ \case
        Right False -> F.PFalse
        Right True  -> F.PTrue
        Left  e     -> e
    Left ie -> do
      na <- normalise t a
      checkGuardPure na $ \case
        Right False -> normaliseNot i
        Right True  -> F.PTrue
        Left  e     -> F.PImp ie e

normaliseIff
  :: (MonadReader NBEEnv m, MonadState NBEState m)
  => Maybe SpecType
  -> Expr
  -> Expr
  -> m (NBEResult Expr)
normaliseIff t l r = do
  nl <- normalise t l
  nr <- normalise t r
  checkGuardPure2 nl nr $ \case
    (Right b  ,  Right b')
      | b == b'   -> F.PTrue
      | otherwise -> F.PFalse
    (Right True  , Left e) -> e
    (Right False , Left e) -> normaliseNot e
    (Left e ,  Right True) -> e
    (Left e , Right False) -> normaliseNot e
    (Left e   ,   Left e') -> F.PIff e e'

normaliseTest :: MonadReader NBEEnv m => Symbol -> Expr -> m Expr
normaliseTest tst e
  = case fst (F.splitEApp e) of
      F.EVar v
        | F.testSymbol v == tst -> return F.PTrue
        | otherwise             -> do
            isDC <- isDataCons v
            return $ if isDC then F.PFalse else F.EApp (F.EVar tst) (F.EVar v)
      _ -> return $ F.EApp (F.EVar tst) e

normaliseSelector :: Symbol -> (Symbol, Int) -> Expr -> Expr
normaliseSelector sel (dc, n) a@(F.EApp e1 e2)
  = case getAppArgs e1 e2 of
      (F.EVar v , as)
        | v == dc -> as !! n
      _ -> F.EApp (F.EVar sel) a
normaliseSelector sel _ a = F.EApp (F.EVar sel) a

normaliseNot :: Expr -> Expr
normaliseNot F.PTrue    = F.PFalse
normaliseNot F.PFalse   = F.PTrue
normaliseNot (F.PNot e) = e
normaliseNot e          = F.PNot e

normaliseNeg :: Expr -> Expr
normaliseNeg (F.ECon (F.I n)) = F.ECon (F.I (- n))
normaliseNeg (F.ECon (F.R x)) = F.ECon (F.R (- x))
normaliseNeg e                = F.ENeg e

normaliseITE
  :: (MonadReader NBEEnv m, MonadState NBEState m)
  => Maybe SpecType
  -> Expr
  -> Expr
  -> Expr
  -> m (NBEResult Expr)
normaliseITE t p ib eb = do
  let (cp, ci, ce) = contractIfThenElse p ib eb
  np <- normalise (Just boolType) cp

  checkGuard np $ \case
    Right True  -> normalise t ci
    Right False -> normalise t ce
    Left p'     -> do
      ni <- withGuard p' $ normalise t ci
      ne <- withGuard (normaliseNot p') $ normalise t ce
      forEachPure2 ni ne (F.EIte p')

contractIfThenElse :: Expr -> Expr -> Expr -> (Expr, Expr, Expr)
contractIfThenElse p i@(F.EIte q ti te) e
  | te == e   = contractIfThenElse (mergeAnd p q) ti e
  | otherwise = case e of
      F.EIte r fi fe
        | fi == i   -> contractIfThenElse (mergeOr p r) i fe
        | otherwise -> (p, i, e)
      _ -> (p, i, e)
contractIfThenElse p i e@(F.EIte q fi fe)
  | fi == i   = contractIfThenElse (mergeOr p q) i fe
  | otherwise = (p, i, e)
contractIfThenElse p i e = (p, i, e)

-- | Resolves the join type constructors in a data constructor argument list
resolveJoins :: Maybe SpecType -> [SpecType] -> [SpecType]
resolveJoins (Just (LH.RApp tc@(LH.QTyCon {}) _ _ _))
  = map (LH.mapTyCon updateJoin)
    where
      updateJoin LH.JoinTyCon {} = tc
      updateJoin x               = x
resolveJoins _ = id

canPropagateRelType :: Brel -> Bool
canPropagateRelType F.Eq = False
canPropagateRelType F.Ne = False
canPropagateRelType _    = True

-----------------------------------------------------------------------
--  Rewrite utility functions
-----------------------------------------------------------------------

getRewritesWith
  :: Expr
  -> (QuotientRewrite -> Maybe (RewriteResult Expr))
  -> [QuotientRewrite]
  -> NBEResult Expr
getRewritesWith e getResult
  = go $ NBEResult
      [ RWResult
          { rwCondition   = Nothing
          , rwResult      = e
          , rwQuantifiers = mempty
          }
      ]
    where
      go :: NBEResult Expr -> [QuotientRewrite] -> NBEResult Expr
      go r@(NBEResult _)  [] = r
      go r@(NBEResult rs) (rw : rws)
        = case getResult rw of
            Nothing  -> go r rws
            Just res -> go (NBEResult $ res : rs) rws

litRewrites :: Constant -> [QuotientRewrite] -> NBEResult Expr
litRewrites c = getRewritesWith (F.ECon c) getResult
  where
    getResult :: QuotientRewrite -> Maybe (RewriteResult Expr)
    getResult CG.QuotientRewrite {..}
      = case rwPattern of
          F.QPLit c'
            | c == c' ->
                Just $ RWResult
                  { rwCondition   = rwPrecondition
                  , rwResult      = rwExpr
                  , rwQuantifiers = rwFreeVars
                  }
            | otherwise -> Nothing
          _ -> Nothing

varRewrites :: Symbol -> [QuotientRewrite] -> NBEResult Expr
varRewrites s = getRewritesWith (F.EVar s) getResult
  where
    getResult :: QuotientRewrite -> Maybe (RewriteResult Expr)
    getResult CG.QuotientRewrite {..}
      = case rwPattern of
          F.QPVar v ->
            Just $ RWResult
              { rwCondition   = rwPrecondition
              , rwResult      = F.subst1 rwExpr (v, F.EVar s)
              , rwQuantifiers = S.delete v rwFreeVars
              }
          _ -> Nothing

conRewrites
  :: HashSet Symbol    -- | Free variables
  -> Expr              -- | Data constructor application expression
  -> Symbol            -- | Data constructor that was applied
  -> [Expr]            -- | Arguments to data constructor
  -> [QuotientRewrite] -- | Rewrites that can be applied
  -> NBEResult Expr
conRewrites fvs app c as = getRewritesWith app getResult
  where
    getResult :: QuotientRewrite -> Maybe (RewriteResult Expr)
    getResult CG.QuotientRewrite {..}
      = case rwPattern of
          F.QPVar v ->
            Just $ RWResult
              { rwCondition   = rwPrecondition
              , rwResult      = F.subst1 rwExpr (v, app)
              , rwQuantifiers = S.delete v rwFreeVars
              }
          F.QPCons m c' ps
            | m == length as && c == c' -> do
                sub <- subsumesAll (S.union fvs rwFreeVars) ps as
                Just $ RWResult
                  { rwCondition   = rwPrecondition
                  , rwResult      = F.subst (F.Su sub) rwExpr
                  , rwQuantifiers = S.difference rwFreeVars (M.keysSet sub)
                  }
            | otherwise -> Nothing
          _ -> Nothing

subsumesAll :: HashSet Symbol -> [QPattern] -> [Expr] -> Maybe (HashMap Symbol Expr)
subsumesAll fvs ps es = do
  Fold.foldlM
    (\sub (np, ne) -> do
        nsub <- subsumes fvs np ne
        F.mergeSubst fvs sub nsub
    ) mempty (zip ps es)

subsumes :: HashSet Symbol -> QPattern -> Expr -> Maybe (HashMap Symbol Expr)
subsumes _ (F.QPLit c) (F.ECon c')
  | c == c'   = Just mempty
  | otherwise = Nothing
subsumes fvs (F.QPVar v) e
  | S.member v fvs = Just (M.singleton v e)
  | otherwise      = Nothing
subsumes fvs (F.QPCons n c ps) (F.EApp e a)
  = case getAppArgs e a of
      (F.EVar c', as)
        | c' == c && length as == n -> subsumesAll fvs ps as
        | otherwise                 -> Nothing
      _ -> Nothing
subsumes _ _ _ = Nothing

-----------------------------------------------------------------------
--  Constructing an expression from result of NBE
-----------------------------------------------------------------------

data Condition
  = AlwaysFalse
  | AlwaysTrue
  | Condition Expr
  deriving Show

mapCondition :: (Expr -> Expr) -> Condition -> Condition
mapCondition f (Condition e) = Condition (f e)
mapCondition _ c             = c

isAlwaysTrue :: Condition -> Bool
isAlwaysTrue AlwaysTrue = True
isAlwaysTrue _          = False

getConditionExpr :: Condition -> Maybe Expr
getConditionExpr (Condition e) = Just e
getConditionExpr _             = Nothing

makeRespectCondition :: NBEResult Expr -> NBEResult Expr -> Maybe Expr
makeRespectCondition (NBEResult lhs) (NBEResult rhs)
  = if trace (show conditions) alwaysRespects then
      Nothing
    else case MB.mapMaybe getConditionExpr conditions of
      []  -> Nothing
      [e] -> Just e
      es  -> Just $ F.POr es
    where
      alwaysRespects :: Bool
      alwaysRespects = Fold.any isAlwaysTrue conditions

      conditions :: [Condition]
      conditions = [ makeCondition l r | l <- lhs, r <- rhs ]

      makeCondition :: RewriteResult Expr -> RewriteResult Expr -> Condition
      makeCondition l r
        = case (rwCondition l, rwCondition r) of
            (Nothing , Nothing) ->
                makeEquality (rwResult l) (rwResult r)
            (Just p  , Just q ) ->
              addPrecondition (mergePreconditions p q)
                $ makeEquality (rwResult l) (rwResult r)
            (Just p  , Nothing) ->
              addPrecondition p
                $ makeEquality (rwResult l) (rwResult r)
            (Nothing , Just q ) ->
              addPrecondition q
                $ makeEquality (rwResult l) (rwResult r)

      addPrecondition :: Expr -> Condition -> Condition
      addPrecondition F.PFalse _ = AlwaysFalse
      addPrecondition F.PTrue  c = c
      addPrecondition pc       c = mapCondition (F.PImp pc) c

      makeEquality :: Expr -> Expr -> Condition
      makeEquality x y
        | x == y    = AlwaysTrue
        | otherwise = Condition $ F.PAtom F.Eq x y

-- | Check if a conjunction of expressions leads to a contradiction
isContradiction :: [Expr] -> Bool
isContradiction es
  = Fold.any (\x ->
      Fold.any (\y ->
        x `implies` F.PNot y || y `implies` F.PNot x
      ) es
    ) es

-- | Check if a disjunction of expression is a tautology
isTautology :: [Expr] -> Bool
isTautology es
  = Fold.all (\x ->
      Fold.any (\y ->
        x `implies` F.PNot y || y `implies` F.PNot y
      ) es
    ) es

makeOr :: [Expr] -> Expr
makeOr [e] = e
makeOr es  = F.POr es

mergePreconditions :: Expr -> Expr -> Expr
mergePreconditions (F.PAnd ps) (F.PAnd qs)
  = case ps' ++ qs' of
      [r] -> r
      rs  -> if isContradiction rs then F.PFalse else F.PAnd rs
    where
      ps' = filter (\p -> not $ Fold.any (`implies` p) qs) ps
      qs' = filter (\q -> not $ Fold.any (`implies` q) ps') qs
mergePreconditions (F.POr ps) (F.POr qs)
  = case (isTautology ps', isTautology qs') of
      (True  , True ) -> F.PTrue
      (True  , False) -> makeOr qs'
      (False , True ) -> makeOr ps'
      (False , False) -> F.PAnd [makeOr ps', makeOr qs']
    where
      ps' = filter (\p -> not $ Fold.all (`implies` p) qs) ps
      qs' = filter (\q -> not $ Fold.all (`implies` q) ps') qs
mergePreconditions (F.PAnd ps) p = F.PAnd (p : ps)
mergePreconditions p (F.PAnd ps) = F.PAnd (p : ps)
mergePreconditions p q = F.PAnd [p, q]

-----------------------------------------------------------------------
--  Quotient respectability checking
-----------------------------------------------------------------------

data AltUnifier
  = AltWasSubsumed !Symbol !QPattern
  | AltDidSubsume !(HashMap Symbol QPattern)

data QuotientCase
  = QuotientCase
      { scrutinee       :: !GHC.Var
        -- | ^ The bound variable (scrutinee)
      , quotientType    :: !SpecQuotientType
        -- | ^ The (quotient) type of the scrutinee
      , altCases        :: ![CoreAlt]
        -- | ^ The case alternatives
      , altEnvironments :: ![CGEnv]
        -- | ^ The environments of each case alternative body
      , ghcCaseType     :: !GHC.Type
        -- | ^ The GHC type of the case body
      , caseType        :: !SpecType
        -- | ^The refined type of the case body
      }

initNBEEnv :: CGEnv -> CG NBEEnv
initNBEEnv γ = do
  rs <- ST.gets getReflects
  ss <- ST.gets getSelectors
  dc <- ST.gets getDataCons
  return NBE
    { nbeDefs      = rs
    , nbeSelectors = ss
    , nbeDataCons  = dc
    , nbeGuards    = []
    , nbeRewrites  = CG.cgQuotRewrites γ
    }
  where
    getReflects :: CG.CGInfo -> HashMap Symbol NBEDefinition
    getReflects
      = M.fromList
      . map mkNBEDefinition
      . LH.gsHAxioms
      . LH.gsRefl
      . LH.giSpec
      . CG.ghcI

    getSelectors :: CG.CGInfo -> HashMap Symbol (Symbol, Int)
    getSelectors
      = M.fromList
      . MB.mapMaybe makeSel
      . concatMap makeSimplify
      . CG.dataConTys

    getDataCons :: CG.CGInfo -> HashMap Symbol SpecType
    getDataCons
      = M.fromList
      . map (first F.symbol)
      . CG.dataConTys

    mkNBEDefinition :: (Var, LocSpecType, Equation) -> (Symbol, NBEDefinition)
    mkNBEDefinition (v, t, F.Equ {..})
      = ( F.symbol v
        , NBEDefinition
            { nbeUnfoldTotal = 0
            , nbeType        = F.val t
            , nbeDefinition  = foldr F.ELam eqBody eqArgs
            }
        )

    makeSel :: F.Rewrite -> Maybe (Symbol, (Symbol, Int))
    makeSel rw
      | F.EVar x <- F.smBody rw
          = (F.smName rw,) . (F.smDC rw,) <$> L.elemIndex x (F.smArgs rw)
      | otherwise = Nothing

performQuotientChecks
  :: CGEnv
  -> GHC.Var
  -> [CoreAlt]
  -> [CGEnv]
  -> GHC.Type
  -> SpecType
  -> CG ()
performQuotientChecks γ x alts γs τ ty
  = whenJust (CG.lookupREnv (F.symbol x) (CG.renv γ)) $ \case
      LH.RApp (LH.QTyCon nm _ _ _ _ _) _ _ _ ->
        whenJust (M.lookup (F.val nm) (CG.cgQuotTyCons γ))
        $ \qty ->
            checkRespectfulness γ
              $ QuotientCase
                  { scrutinee       = x
                  , quotientType    = qty
                  , altCases        = alts
                  , altEnvironments = γs
                  , ghcCaseType     = τ
                  , caseType        = ty
                  }
      _                                -> return ()

checkRespectfulness :: CGEnv -> QuotientCase -> CG ()
checkRespectfulness γ QuotientCase {..} = do
  lc     <- caseBody
  nbeEnv <- initNBEEnv γ
  let alts = zip altEnvironments altCases
  Fold.traverse_ (uncurry $ checkAlt nbeEnv lc quotients) alts
  where
    -- | Translated to an open term with `scrutinee` as a free variable
    ghcCase :: CoreExpr
    ghcCase = GHC.Case (GHC.Var scrutinee) scrutinee ghcCaseType altCases

    scrutineeSym :: Symbol
    scrutineeSym = F.symbol scrutinee

    caseBody :: CG Expr
    caseBody
      = unsafeCoreToLogic γ
          ("Failed to translate GHC case body to CoreExpr: " ++)
          ghcCase

    quotients :: [SpecQuotient]
    quotients
      = MB.mapMaybe
          (`M.lookup` CG.cgQuotients γ)
          (LH.qtyQuots quotientType)

    checkAlt :: NBEEnv -> Expr -> [SpecQuotient] -> CGEnv -> CoreAlt -> CG ()
    checkAlt nbeEnv ce qs cγ alt = Fold.traverse_ (checkRespects nbeEnv cγ ce alt) qs

    makeAltExpr :: CoreExpr -> CG Expr
    makeAltExpr ae
      = unsafeCoreToLogic γ
          ("Failed to translate GHC case alternative to CoreExpr: " ++) ae

    checkRespects
      :: NBEEnv
      -> CGEnv
      -> Expr
      -> CoreAlt
      -> SpecQuotient
      -> CG ()
    checkRespects nbeEnv cγ ce (GHC.Alt ac bs ae) LH.Quotient {..} = do
      let freeEnv = CG.toMapREnv (CG.renv cγ)
          qsym    = F.val qtName
      whenJust (unifyAlt (M.keysSet qtVars) (F.val qtLeft) ac bs) $ \case
        AltWasSubsumed v p -> do
          let domain = M.delete v qtVars
              rhs    = F.subst1 (F.val qtRight) (v, F.expr p)

          γ'  <- Fold.foldlM CG.addEEnv cγ $ M.toList domain
          lhs <- makeAltExpr ae

          doCheck nbeEnv γ' qsym (M.union freeEnv domain) ce lhs rhs
        AltDidSubsume sub  -> do
          γ'  <- Fold.foldlM CG.addEEnv cγ $ M.toList qtVars
          lhs <- F.subst (F.Su $ F.expr <$> sub) <$> makeAltExpr ae

          doCheck nbeEnv γ' qsym (M.union freeEnv qtVars) ce lhs $ F.val qtRight

    doCheck
      :: NBEEnv
      -> CGEnv
      -> Symbol
      -> HashMap Symbol SpecType
      -> Expr
      -> Expr
      -> Expr
      -> CG ()
    doCheck nbeEnv cγ qsym fvs f lhs rhs = do
      let frhs      = F.subst1 f (scrutineeSym, rhs)
          st        = NBEState (KnownType <$> fvs)
          lResult   = normaliseWithEnv nbeEnv st caseType lhs
          rResult   = normaliseWithEnv nbeEnv st caseType frhs
          condition = makeRespectCondition lResult rResult
      whenJust condition $ mkConstraint cγ qsym ""

    mkConstraint :: CGEnv -> Symbol -> String -> F.Expr -> CG ()
    mkConstraint γ' qsym msg p
      = CG.addC (CG.SubR γ' (LH.OQuot qsym) $ LH.uReft (F.vv_, p)) msg

normaliseWithEnv :: NBEEnv -> NBEState -> SpecType -> Expr -> NBEResult Expr
normaliseWithEnv env st t e
  = ST.evalState (RD.runReaderT (normalise (Just t) e) env) st

unsafeCoreToLogic :: CGEnv -> (String -> String) -> CoreExpr -> CG Expr
unsafeCoreToLogic γ em ce = do
  adts <- ST.gets CG.cgADTs
  let dm = Bare.dataConMap adts
      le = CL.coreToLogic True ce

  case CL.runToLogic (CG.emb γ) mempty dm (LH.todo Nothing . em) le of
    Left  err -> error $ show err
    Right ex  -> return ex

unifyAlt :: HashSet Symbol -> QPattern -> AltCon -> [CoreBndr] -> Maybe AltUnifier
unifyAlt fvs (F.QPVar v) alt bs
  | S.member v fvs
      = case alt of
          GHC.LitAlt (GHC.LitNumber _ n) ->
            Just $ AltWasSubsumed v $ F.QPLit (F.I n)
          GHC.LitAlt (GHC.LitDouble x)   ->
            Just $ AltWasSubsumed v $ F.QPLit (F.R $ fromRational x)
          GHC.LitAlt (GHC.LitFloat x)    ->
            Just $ AltWasSubsumed v $ F.QPLit (F.R $ fromRational x)
          GHC.LitAlt (GHC.LitChar c)     ->
            Just $ AltWasSubsumed v $ F.QPLit (F.L (Text.singleton c) F.charSort)
          GHC.LitAlt (GHC.LitString s)   ->
            Just $ AltWasSubsumed v $ F.QPLit (F.L (Text.decodeUtf8 s) F.strSort)
          GHC.DataAlt c                  ->
            Just $ AltWasSubsumed v
              $ F.QPCons (length bs) (dcSymbol c) $ map (F.QPVar . F.symbol) bs
          _                              -> Nothing
  | otherwise = Nothing
unifyAlt _ (F.QPLit (F.I m)) (GHC.LitAlt (GHC.LitNumber _ n)) _
  | m == n    = Just $ AltDidSubsume mempty
  | otherwise = Nothing
unifyAlt _ (F.QPLit (F.R x)) (GHC.LitAlt (GHC.LitDouble y)) _
  | x == fromRational y = Just $ AltDidSubsume mempty
  | otherwise           = Nothing
unifyAlt _ (F.QPLit (F.R x)) (GHC.LitAlt (GHC.LitFloat y)) _
  | x == fromRational y = Just $ AltDidSubsume mempty
  | otherwise           = Nothing
unifyAlt _ (F.QPLit (F.L c s)) (GHC.LitAlt (GHC.LitChar c')) _
  | F.isChar s && Text.head c == c' = Just $ AltDidSubsume mempty
  | otherwise                       = Nothing
unifyAlt _ (F.QPLit (F.L str s)) (GHC.LitAlt (GHC.LitString str')) _
  | F.isString s && Text.decodeUtf8 str' == str = Just $ AltDidSubsume mempty
  | otherwise                                   = Nothing
unifyAlt _ (F.QPCons m c ps) (GHC.DataAlt c') bs
  | m == length bs && c == dcSymbol c'
      = Just $ AltDidSubsume (M.fromList $ zipWith (\b p -> (F.symbol b, p)) bs ps)
  | otherwise = Nothing
unifyAlt _ _ _ _ = Nothing

dcSymbol :: GHC.DataCon -> F.Symbol
dcSymbol = F.symbol . GHC.dataConWorkId
