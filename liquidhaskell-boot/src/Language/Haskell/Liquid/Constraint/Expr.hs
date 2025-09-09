{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}

-- | Bidirectional type checking for refinement expressions.
--
-- Notably, unlike type-checking for GHC CoreExpr's defined in Generate.hs, it is not
-- the case that generalisation and instantiation of polymorphic type variables is
-- reflected in the syntax of refinement expressions. Therefore, they must be handled
-- explicitly alongside predicate and quotient variables.

module Language.Haskell.Liquid.Constraint.Expr
  ( cconsExpr
  ) where

import           Control.Monad                                   (foldM, when)
import qualified Control.Monad.Reader                            as Reader
import           Control.Monad.State.Strict                      (MonadState, State, StateT)
import qualified Control.Monad.State.Strict                      as State
import qualified Control.Monad.Except                            as Error
import qualified Data.Char                                       as Char
import           Data.Foldable                                   (foldrM, traverse_)
import           Data.Functor                                    (($>))
import qualified Data.HashMap.Internal                           as HashMapI
import           Data.HashMap.Strict                             (HashMap)
import qualified Data.HashMap.Strict                             as HashMap
import           Data.HashSet                                    (HashSet)
import qualified Data.HashSet                                    as HashSet
import           Data.IntMap.Strict                              (IntMap)
import qualified Data.IntMap.Strict                              as IntMap
import qualified Data.Maybe                                      as Maybe
import qualified Data.Text                                       as Text

import           GHC.Types.SrcLoc                                (SrcSpan)

import qualified Language.Fixpoint.SortCheck                     as Fixpoint
import           Language.Fixpoint.Types
  ( Brel
  , Constant
  , Expr
  , Expression
  , ExprV
  , FTycon
  , Reft
  , Sort
  , Symbol
  )
import qualified Language.Fixpoint.Types                         as Fixpoint
import qualified Language.Fixpoint.Types.PrettyPrint             as Pretty
import qualified Language.Fixpoint.Types.Visitor                 as FixVisit
import           Language.Haskell.Liquid.Constraint.Env          ((?=), (+=))
import qualified Language.Haskell.Liquid.Constraint.Env          as Environment
import qualified Language.Haskell.Liquid.Constraint.Fresh        as Fresh
import           Language.Haskell.Liquid.Constraint.Instantiate
  ( QVarInst
  , TypeInst
  , Quantified
  )
import qualified Language.Haskell.Liquid.Constraint.Instantiate  as Instantiate
import qualified Language.Haskell.Liquid.Constraint.Monad        as Constraint
import qualified Language.Haskell.Liquid.Constraint.Sort         as Sort
import qualified Language.Haskell.Liquid.Constraint.Substitution as Substitution
import           Language.Haskell.Liquid.Constraint.Types        (CG, CGEnv, CGInfo)
import qualified Language.Haskell.Liquid.Constraint.Types        as Constraint
import           Language.Haskell.Liquid.Constraint.Unification
  ( UnifyResult
  , UnifySession
  , UnifyTypeRep
  )
import qualified Language.Haskell.Liquid.Constraint.Unification  as Unification
import qualified Language.Haskell.Liquid.GHC.Misc                as GM
import           Language.Haskell.Liquid.Types.AntiUnify         (AUTypeRep, FromInt (..))
import qualified Language.Haskell.Liquid.Types.AntiUnify         as AntiUnify
import qualified Language.Haskell.Liquid.Types.Errors            as Error
import qualified Language.Haskell.Liquid.Types.Fresh             as Fresh
import qualified Language.Haskell.Liquid.Types.PredType          as Liquid
import           Language.Haskell.Liquid.Types.QuotDecl          (EqualityParamP)
import qualified Language.Haskell.Liquid.Types.QuotDecl          as Quotient
import qualified Language.Haskell.Liquid.Types.QuotSubst         as Quotient
import qualified Language.Haskell.Liquid.Types.RefType           as Liquid
import           Language.Haskell.Liquid.Types.RType
  ( PVar
  , QVarKind
  , RReft
  , RSort
  , RTyCon
  , RTypeV
  , RTyVar
  , SpecProp
  , SpecQVar
  , SpecRTVar
  , SpecType
  , UReftV
  )
import qualified Language.Haskell.Liquid.Types.RType             as Liquid
import qualified Language.Haskell.Liquid.Types.RTypeOp           as Liquid
import           Language.Haskell.Liquid.Types.Types             (Error)
import qualified Language.Haskell.Liquid.Types.Types             as Liquid
import qualified Language.Haskell.Liquid.UX.Config               as Config

import           Liquid.GHC.API                                  (CoreExpr)
import qualified Liquid.GHC.API                                  as GHC

import           Text.PrettyPrint.HughesPJ                       (Doc, (<+>))
import qualified Text.PrettyPrint.HughesPJ                       as Pretty

newtype ImplicitLookup a
  = ImplicitLookup
      { runLookup :: ExprCG (SpecType, a)
      } deriving Functor

type SpecTypeRep = UnifyTypeRep RTyCon RTyVar RReft
type SpecAUType  = AUTypeRep Symbol RTyCon RTyVar ()

data VarKind
  = Explicit
  | Implicit

data LookupResult
  = Found !SpecType
  | NotFound

data CGState
  = CGState
      { unifySession :: !(UnifySession RTyCon RTyVar RReft)
      , implicitVars :: !(HashMap Symbol SpecType)
      , instTypeVars :: !(HashMap RTyVar TypeInst)
      , instQuotVars :: !(HashMap Symbol QVarInst)
      }

type ExprCG         = StateT CGState CG
type QuantifiedType = ([(SpecRTVar, RReft)], [PVar RSort], [(SpecQVar, RReft)], SpecType)

adjustOrInsertF :: (v -> f v) -> k -> f v -> HashMap k v -> f (HashMap k v)
adjustOrInsertF f !k !v !m
  = let !h          = HashMapI.hash k
        inserts !v' = HashMapI.insert' h k v' m
     in case HashMapI.lookup' h k m of
          Nothing -> inserts <$> v
          Just v' -> inserts <$> f v'

modifyM :: MonadState s m => (s -> m s) -> m ()
modifyM f = do
  s <- State.get
  f s >>= State.put

locally :: MonadState s m => (s -> s) -> m a -> m a
locally f m = do
  s <- State.get
  (State.put $! f s) *> m <* State.put s

zipWithAndThenM
  :: Applicative f
  => (a -> b -> f c)
  -> ([a] -> f [c])
  -> ([b] -> f [c])
  -> [a] -> [b] -> f [c]
zipWithAndThenM _ _  _  []       []       = pure []
zipWithAndThenM f fa fb (a : as) (b : bs) = (:) <$> f a b <*> zipWithAndThenM f fa fb as bs
zipWithAndThenM _ fa _  as       []       = fa as
zipWithAndThenM _ _  fb []       bs       = fb bs

exprUReft :: Expression a => a -> UReftV v Reft
exprUReft = Liquid.uTop . Fixpoint.exprReft

splitEApp :: ExprV v -> ExprV v -> (ExprV v, [ExprV v])
splitEApp f a = go [a] f
  where
    go acc (Fixpoint.EApp g e) = go (e:acc) g
    go acc e                   = (e, acc)

supportTypeclass :: CGEnv -> Bool
supportTypeclass = Config.typeclass . Config.getConfig

addPToEnv :: CGEnv -> PVar RSort -> CG CGEnv
addPToEnv γ π = do
  γπ <- γ += ("addSpec1", Liquid.pname π, Liquid.pvarRType π)
  foldM (+=) γπ [("addSpec2", x, Liquid.ofRSort t) | (t, x, _) <- Liquid.pargs π]

checkImplicit
  :: SrcSpan
  -> String
  -> UnifySession RTyCon RTyVar RReft
  -> SpecType
  -> SpecType
  -> ExprCG SpecType
checkImplicit p s us τ τ'
  = case Error.runExcept $ Unification.unifyInSession p s us τ' τ of
      Left  e -> State.lift (Constraint.addWarning e) $> τ'
      Right Unification.UnifyResult {..} ->
        State.modify' (\st -> st { unifySession = unSession }) $> unSkeleton

addImplicitType
  :: SrcSpan
  -> Symbol
  -> UnifySession RTyCon RTyVar RReft
  -> SpecType
  -> HashMap Symbol SpecType
  -> ExprCG (HashMap Symbol SpecType)
addImplicitType p k us τ m
  = adjustOrInsertF (checkImplicit p "cconsExpr: type-checking error" us τ) k (pure τ) m

(??=) :: CGEnv -> Symbol -> ExprCG LookupResult
γ ??= x
  | Just varType <- γ ?= x = pure $ Found τ
  | otherwise
      = State.gets \CGState {implicitVars} ->
          maybe NotFound Found $ HashMap.lookup x implicitVars

quantify :: SpecType -> CGState -> Quantified
quantify instType CGState { instTypeVars, instQuotVars }
  = Instantiate.instantiate Instantiate.Instantiated
      { instTVs  = instTypeVars
      , instQVs  = instQuotVars
      , ..
      }

cconsFunApp :: CGEnv -> [Expr] -> SpecType -> ExprCG SpecType
cconsFunApp _ [] τ = pure τ
cconsFunApp γ (a : as) Liquid.RFun {..} = do
  cconsExprPoly γ a rt_in
  cconsFunApp γ as $ Fixpoint.subst1 rt_out (rt_bind, a)
cconsFunApp γ (a : as) Liquid.RVar {..} = x -- | Inst
cconsFunApp γ as@(_ : _) τ = x

lookupApplication :: CGEnv -> Symbol -> [Expr] -> ExprCG Quantified
lookupApplication γ x as
  = γ ??= x >>= \case
      Found τ -> do
        Instantiate.Instantiated {..} <- State.lift $ Instantiate.freshInstType γ τ
        st <- State.get
        State.put st { instTypeVars = instTVs, instQuotVars = instQVs }
        τ' <- cconsFunApp γ as instType
        rτ <- quantify τ' <$> State.get
        State.put st $> rτ

      NotFound -> do
        st                                   <- State.get
        State.put st { instTypeVars = HashMap.empty, instQuotVars = HashMap.empty }
        τs                                   <- traverse (consExpr γ) as
        α                                    <- Fresh.fresh
        CGState {unifySession, implicitVars} <- State.get
        let baseType = Liquid.RVar { rt_var = α, rt_reft = mempty }
            mkRFun   = Liquid.rFun Fixpoint.dummySymbol
        State.put st
          { unifySession = Unification.addTypeVarToSession α unifySession
          , implicitVars = HashMap.insert x (foldr mkRFun baseType τs) implicitVars
          } $> Instantiate.Quantified { typeVars = [], quotVars = [], .. }

addCConstraint :: CGEnv -> String -> SpecType -> SpecType -> ExprCG ()
addCConstraint senv e lhs rhs
  = State.lift
  $ Constraint.addC Constraint.SubC {..}
  $  "cconsExpr: " ++ "\n lhs = " ++ Fixpoint.showpp lhs
  ++ "\n rhs = " ++ Fixpoint.showpp rhs ++ e

alterImplicitVars
  :: (HashMap Symbol SpecTypeRep -> ExprCG (HashMap Symbol SpecTypeRep)) -> ExprCG ()
alterImplicitVars f
  = modifyM \st@CGState{implicitVars} -> (\ivs -> st { implicitVars = ivs }) <$> f implicitVars

lookupImplicit :: SrcSpan -> String -> SpecType -> Maybe SpecTypeRep -> ImplicitLookup (Maybe SpecTypeRep)
lookupImplicit _ _ τ Nothing = ImplicitLookup $ pure (τ, Just $ Unification.toUnifyTypeRep τ)
lookupImplicit p s τ (Just τ')
  = ImplicitLookup do
      let ue = Error.runExcept $ Unification.unifyRepWithType p s τ' τ
      case ue of
        Left  e -> State.lift (Constraint.addWarning e) $> (τ, Nothing)
        Right t -> pure (Unification.fromUnifyTypeRep t, Just t)

illTypedError :: CGEnv -> Expr -> SpecType -> Doc -> a
illTypedError γ e t msg
  = Error.panic Nothing $ show $ Pretty.pprint Error.ErrIlltypedExpr
      { pos          = Constraint.getLocation γ
      , expression   = Pretty.pprint e
      , expectedType = Pretty.pprint t
      , msg
      }

consRelation :: CGEnv -> Brel -> Expr -> ExprCG SpecType
consRelation γ Fixpoint.Eq  e = consExpr γ e
consRelation γ Fixpoint.Ne  e = consExpr γ e
consRelation γ Fixpoint.Ueq e = consExpr γ e
consRelation γ Fixpoint.Une e = consExpr γ e
consRelation γ Fixpoint.Gt  e
  = cconsExpr γ e (Sort.integerType mempty) $> Sort.integerType (exprUReft e)
consRelation γ Fixpoint.Ge  e
  = cconsExpr γ e (Sort.integerType mempty) $> Sort.integerType (exprUReft e)
consRelation γ Fixpoint.Lt  e
  = cconsExpr γ e (Sort.integerType mempty) $> Sort.integerType (exprUReft e)
consRelation γ Fixpoint.Le  e
  = cconsExpr γ e (Sort.integerType mempty) $> Sort.integerType (exprUReft e)

cconsApp :: CGEnv -> Expr -> SpecType -> Expr -> [Expr] -> ExprCG ()
cconsApp γ expr τ = go
  where
    go :: Expr -> [Expr] -> ExprCG ()
    go (Fixpoint.EApp f a)      as = go f (a : as)

    go (Fixpoint.EVar v)        as = do
      resType <- lookupApplication γ v as
      s

    go (Fixpoint.ELet x e e')   as = do
      t  <- consExpr γ e
      γ' <- State.lift $ γ += ("", x, t)
      cconsApp γ' e' τ e' as

    go (Fixpoint.ELam (x, t) e) [a] = do
      let xt = Sort.sortToSpecType t mempty
      cconsExprPoly γ a xt
      γ' <- State.lift $ γ += ("", x, xt)
      cconsExpr γ' e τ

    go (Fixpoint.ELam (x, t) e) (a : as) = do
      let xt = Sort.sortToSpecType t mempty
      cconsExprPoly γ a xt
      γ' <- State.lift $ γ += ("", x, xt)
      cconsApp γ' e τ e as

    go (Fixpoint.EIte c i e)    as = do
      cconsBoolExpr γ c
      x
      y

    go (Fixpoint.ESym s)        as = p

    go (Fixpoint.ECst e t)      as = do
      let specType = Sort.sortToSpecType t
      cconsExprPoly γ e $ specType mempty
      x

    go (Fixpoint.ETApp e t)     as = p

    go (Fixpoint.ETAbs e α)     as = p

    go (Fixpoint.PAll xts e)    as = p

    go (Fixpoint.PExist xts e)  as = p

    go e@Fixpoint.PKVar  {} _  = err $ Pretty.pprint e <+> " is not a function"
    go e@Fixpoint.ECoerc {} _  = err $ Pretty.pprint e <+> " is not a function"
    go e@Fixpoint.ECon   {} _  = err $ Pretty.pprint e <+> " is not a function"
    go e@Fixpoint.ENeg   {} _  = err $ Pretty.pprint e <+> " is not a function"
    go e@Fixpoint.EBin   {} _  = err $ Pretty.pprint e <+> " is not a function"
    go e@Fixpoint.PAnd   {} _  = err $ Pretty.pprint e <+> " is not a function"
    go e@Fixpoint.POr    {} _  = err $ Pretty.pprint e <+> " is not a function"
    go e@Fixpoint.PNot   {} _  = err $ Pretty.pprint e <+> " is not a function"
    go e@Fixpoint.PImp   {} _  = err $ Pretty.pprint e <+> " is not a function"
    go e@Fixpoint.PIff   {} _  = err $ Pretty.pprint e <+> " is not a function"
    go e@Fixpoint.PAtom  {} _  = err $ Pretty.pprint e <+> " is not a function"
    go e@Fixpoint.PGrad  {} _  = err $ Pretty.pprint e <+> " is not a function"
    go   Fixpoint.ELam   {} [] = Fixpoint.panic "impossible: cconsApp applied to empty argument list"

    err :: Doc -> StateT s CG ()
    err = illTypedError γ expr τ

cconsLam
  :: CGEnv
  -> [(Symbol, SpecType)]
  -> Expr
  -> SpecType
  -> ExprCG ()
cconsLam γ xts (Fixpoint.ELam (x, t) e) τ = do
  let xt = Sort.sortToSpecType t mempty
  γ' <- State.lift $ γ += ("", x, xt)
  cconsLam γ' ((x, xt):xts) e τ
cconsLam γ xts e τ
  | length xts <= length ty_args = s
  | otherwise                    = s
  where
    Liquid.RTypeRep {..} = Liquid.toRTypeRep τ

cconsBoolExpr :: CGEnv -> Expr -> ExprCG ()
cconsBoolExpr γ = flip (cconsExpr γ) $ Sort.booleanType mempty
{-# INLINE cconsBoolExpr #-}

cconsIntExpr :: CGEnv -> Expr -> ExprCG ()
cconsIntExpr γ = flip (cconsExpr γ) $ Sort.integerType mempty
{-# INLINE cconsIntExpr #-}

cconsExpr :: CGEnv -> Expr -> SpecType -> ExprCG ()
cconsExpr γ e@(Fixpoint.ESym s) τ
  = addCConstraint γ (GM.showPpr s) (Sort.stringType $ exprUReft e) τ

cconsExpr γ e@(Fixpoint.ECon c) τ
  = addCConstraint γ (GM.showPpr c) (Sort.constantType (exprUReft e) c) τ

cconsExpr γ (Fixpoint.EVar v) τ
  | Just t <- γ ?= v = addCConstraint γ (GM.showPpr v) t τ
  | otherwise        = alterImplicitVars $ State.lift . addImplicitType (Constraint.getLocation γ) v τ

cconsExpr γ e@(Fixpoint.EApp f a) τ = cconsApp γ e τ f [a]

cconsExpr γ ne@(Fixpoint.ENeg e) τ = do
  addCConstraint γ (GM.showPpr ne) (Sort.integerType $ exprUReft ne) τ
  cconsIntExpr γ e

cconsExpr γ e@(Fixpoint.EBin _ l r) τ = do
  cconsIntExpr γ l
  cconsIntExpr γ r
  addCConstraint γ (GM.showPpr e) (Sort.integerType $ exprUReft e) τ

cconsExpr γ (Fixpoint.ELet x e e') τ = do
  t  <- consExpr γ e
  γ' <- State.lift $ γ += ("", x, t)
  cconsExpr γ' e' τ

cconsExpr γ (Fixpoint.EIte c i e) τ = do
  cconsBoolExpr γ c
  cconsExpr γ i τ
  cconsExpr γ e τ

cconsExpr γ ec@(Fixpoint.ECst e t) τ = do
  let specType = Sort.sortToSpecType t
  addCConstraint γ (GM.showPpr ec) (specType $ exprUReft e) τ
  cconsExpr γ e (specType mempty)

cconsExpr γ (Fixpoint.ELam (x, t) e) τ = do
  let xt = Sort.sortToSpecType t mempty
  γ' <- State.lift $ γ += ("", x, xt)
  cconsLam γ' [(x, xt)] e τ

cconsExpr γ (Fixpoint.ETApp e t) τ
  = consExpr γ e >>= \case
      Liquid.RAllT {..} -> x
      τ' -> x

cconsExpr γ (Fixpoint.ETAbs e α) Liquid.RAllT {..}
  = cconsExpr γ e
      $ Liquid.subsTyVarMeet'
          ( Liquid.ty_var_value rt_tvbind
          , Liquid.RVar
              { rt_var  = Liquid.RTV $ GM.symbolTyVar α
              , rt_reft = mempty
              }
          ) rt_ty

cconsExpr γ (Fixpoint.ETAbs e _) τ = cconsExpr γ e τ

cconsExpr γ e@(Fixpoint.PAnd es) τ = do
  addCConstraint γ (GM.showPpr e) (Sort.booleanType $ exprUReft e) τ
  traverse_ (cconsBoolExpr γ) es

cconsExpr γ e@(Fixpoint.POr es) τ = do
  addCConstraint γ (GM.showPpr e) (Sort.booleanType $ exprUReft e) τ
  traverse_ (cconsBoolExpr γ) es

cconsExpr γ ne@(Fixpoint.PNot e) τ = do
  addCConstraint γ (GM.showPpr ne) (Sort.booleanType $ exprUReft ne) τ
  cconsBoolExpr γ e

cconsExpr γ ie@(Fixpoint.PImp e e') τ = do
  addCConstraint γ (GM.showPpr ie) (Sort.booleanType $ exprUReft ie) τ
  cconsBoolExpr γ e
  cconsBoolExpr γ e'

cconsExpr γ ie@(Fixpoint.PIff e e') τ = do
  addCConstraint γ (GM.showPpr ie) (Sort.booleanType $ exprUReft ie) τ
  cconsBoolExpr γ e
  cconsBoolExpr γ e'

cconsExpr γ e@(Fixpoint.PAtom re l r) τ = do
  t <- consRelation γ re l
  cconsExpr γ r $ Liquid.topRTypeBase t
  addCConstraint γ (GM.showPpr e) (Sort.booleanType $ exprUReft e) τ

cconsExpr γ (Fixpoint.PAll xts e) τ = do
  γ' <- foldrM (\(x, t) -> State.lift . (+= ("", x, Sort.sortToSpecType t mempty))) γ xts
  cconsExpr γ' e τ

cconsExpr γ (Fixpoint.PExist xts e) τ = do
  γ' <- foldrM (\(x, t) -> State.lift . (+= ("", x, Sort.sortToSpecType t mempty))) γ xts
  cconsExpr γ' e τ

cconsExpr γ Fixpoint.PKVar {} _ = Fixpoint.panic "cconsExpr: PKVar is not yet supported"

cconsExpr γ Fixpoint.PGrad {} _ = Fixpoint.panic "cconsExpr: PGrad is not yet supported"

cconsExpr γ Fixpoint.ECoerc {} _ = Fixpoint.panic "cconsExpr: ECoerc is not yet supported"

cconsExprPoly :: CGEnv -> Expr -> SpecType -> ExprCG ()
cconsExprPoly γ e τ = do
  γ' <- State.lift $ foldM addPToEnv γ πs
  cconsExpr γ' e τ'
  where
    (_, πs, _, τ') = Liquid.bkUniv τ

consApp :: CGEnv -> Expr -> Expr -> [Expr] -> ExprCG SpecType
consApp γ expr = go
  where
    go :: Expr -> [Expr] -> ExprCG SpecType
    go (Fixpoint.EApp f a)      as = go f (a : as)

    go (Fixpoint.EVar v)        as = do
      resType <- lookupApplication γ v as
      s

    go (Fixpoint.ELet x e e')   as = do
      t  <- consExpr γ e
      γ' <- State.lift $ γ += ("", x, t)
      consApp γ' e' e' as

    go (Fixpoint.ELam (x, t) e) [a] = do
      let xt = Sort.sortToSpecType t mempty
      cconsExprPoly γ a xt
      rτ <- consExpr γ (Fixpoint.subst1 e (x, a))
      s

    go (Fixpoint.ELam (x, t) e) (a : as) = do
      let xt = Sort.sortToSpecType t mempty
      cconsExprPoly γ a xt
      go (Fixpoint.subst1 e (x, a)) as

    go (Fixpoint.EIte c i e)    as = p

    go (Fixpoint.ESym s)        as = p

    go (Fixpoint.ECst e t)      as = do
      let specType = Sort.sortToSpecType t
      cconsExprPoly γ e $ specType mempty
      x

    go (Fixpoint.ETApp e t)     as = p

    go (Fixpoint.ETAbs e α)     as = p

    go (Fixpoint.PKVar k σ)     as = p
  
    go (Fixpoint.PAll xts e)    as = p

    go (Fixpoint.PExist xts e)  as = p

    go (Fixpoint.ECoerc t u e)  as = p

    go e@Fixpoint.ECon  {} _  = err $ Pretty.pprint e <+> " is not a function"
    go e@Fixpoint.ENeg  {} _  = err $ Pretty.pprint e <+> " is not a function"
    go e@Fixpoint.EBin  {} _  = err $ Pretty.pprint e <+> " is not a function"
    go e@Fixpoint.PAnd  {} _  = err $ Pretty.pprint e <+> " is not a function"
    go e@Fixpoint.POr   {} _  = err $ Pretty.pprint e <+> " is not a function"
    go e@Fixpoint.PNot  {} _  = err $ Pretty.pprint e <+> " is not a function"
    go e@Fixpoint.PImp  {} _  = err $ Pretty.pprint e <+> " is not a function"
    go e@Fixpoint.PIff  {} _  = err $ Pretty.pprint e <+> " is not a function"
    go e@Fixpoint.PAtom {} _  = err $ Pretty.pprint e <+> " is not a function"
    go e@Fixpoint.PGrad {} _  = err $ Pretty.pprint e <+> " is not a function"
    go   Fixpoint.ELam  {} [] = Fixpoint.panic "impossible: cconsApp applied to empty argument list"

    err :: Doc -> StateT s CG SpecType
    err = illTypedError γ expr s

consExpr :: CGEnv -> Expr -> ExprCG SpecType
consExpr γ (Fixpoint.ESym s) = x

consExpr _ e@(Fixpoint.ECon c) = pure $ Sort.constantType (exprUReft e) c

consExpr γ (Fixpoint.EVar v)
  = x

consExpr γ e@(Fixpoint.EApp f a) = consApp γ e f [a]

consExpr γ ne@(Fixpoint.ENeg e)
  = cconsIntExpr γ e $> Sort.integerType (exprUReft ne)

consExpr γ e@(Fixpoint.EBin _ l r) = do
  cconsIntExpr γ l
  cconsIntExpr γ r $> Sort.integerType (exprUReft e)

consExpr γ (Fixpoint.ELet x e e') = do
  t  <- consExpr γ e
  γ' <- State.lift $ γ += ("", x, t)
  consExpr γ' e'

consExpr γ (Fixpoint.EIte c i e) = do
  cconsBoolExpr γ c
  iτ <- consExpr γ i
  eτ <- consExpr γ e
  p

consExpr γ (Fixpoint.ECst e t) = do
  let xt = Sort.sortToSpecType t
  cconsExpr γ e (xt mempty) $> xt (exprUReft e)

consExpr γ (Fixpoint.ELam (x, t) e) = do
  let xt = Sort.sortToSpecType t mempty
  γ' <- State.lift $ γ += ("", x, xt)
  makeRFun xt <$> consExpr γ' e
  where
    makeRFun rt_in rt_out
      = Liquid.RFun
          { rt_in
          , rt_out
          , rt_bind  = x
          , rt_rinfo = Liquid.defRFInfo
          , rt_reft  = mempty
          }

consExpr γ e'@(Fixpoint.ETApp e t)
  = consExpr γ e >>= \case
      Liquid.RAllT {..} ->
        pure
          $ Liquid.subsTyVarMeet'
              (Liquid.ty_var_value rt_tvbind, Sort.sortToSpecType t mempty) rt_ty
      τ -> illTypedError γ e' τ (Pretty.pprint e <+> " is not a type generalisation") $> τ

consExpr γ e'@(Fixpoint.ETAbs e α) = makeAllT <$> consExpr γ e
  where
    makeAllT rt_ty
      = Liquid.RAllT
          { rt_tvbind
              = Liquid.RTVar
                  { ty_var_value = Liquid.RTV $ GM.symbolTyVar α
                  , ty_var_info  = Liquid.RTVNoInfo False
                  }
          , rt_ref    = exprUReft e'
          , ..
          }

consExpr γ e@(Fixpoint.PAnd es)
  = traverse_ (cconsBoolExpr γ) es $> Sort.booleanType (exprUReft e)

consExpr γ e@(Fixpoint.POr es)
  = traverse_ (cconsBoolExpr γ) es $> Sort.booleanType (exprUReft e)

consExpr γ e@(Fixpoint.PNot e')
  = cconsBoolExpr γ e' $> Sort.booleanType (exprUReft e)

consExpr γ ie@(Fixpoint.PImp e e') = do
  cconsBoolExpr γ e
  cconsBoolExpr γ e' $> Sort.booleanType (exprUReft ie)

consExpr γ ie@(Fixpoint.PIff e e') = do
  cconsBoolExpr γ e
  cconsBoolExpr γ e' $> Sort.booleanType (exprUReft ie)

consExpr γ e@(Fixpoint.PAtom re l r) = do
  lτ <- consRelation γ re l
  rτ <- consExpr γ e
  s
  pure $ Sort.booleanType $ exprUReft e

consExpr γ (Fixpoint.PAll xts e) = do
  γ' <- foldrM (\(x, t) -> State.lift . (+= ("", x, Sort.sortToSpecType t mempty))) γ xts
  consExpr γ' e

consExpr γ (Fixpoint.PExist xts e) = do
  γ' <- foldrM (\(x, t) -> State.lift . (+= ("", x, Sort.sortToSpecType t mempty))) γ xts
  consExpr γ' e

consExpr _ Fixpoint.PKVar {} = Fixpoint.panic "consExpr: PKVar is not yet supported"

consExpr _ Fixpoint.PGrad {} = Fixpoint.panic "consExpr: PGrad is not yet supported"

consExpr _ Fixpoint.ECoerc {} = Fixpoint.panic "consExpr: ECoerc is not yet supported"
