{-# OPTIONS_GHC -Wno-orphans            #-}
{-# LANGUAGE BlockArguments             #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MonoLocalBinds             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE UndecidableInstances       #-}

module Language.Haskell.Liquid.Constraint.Substitution
  ( InsertResult  (..)
  , QuotientSubst (..)
  , QuotVarInsert (..)
  , QuotVarUnify  (..)
  , Substitution  (..)
  , SubstEnv      (..)
  , SubstInsert   (..)
  , SubstResult   (..)
  , UnifyMaybe
  , addQuotVarSubst
  , insertTypeVarSubst
  , unionQuotientVars
  , substitute
  ) where

import           Control.Applicative                             ((<|>))
import           Control.Monad.Except                            (MonadError)
import qualified Control.Monad.Except                            as Error
import           Control.Monad.Reader                            (MonadReader, ReaderT)
import qualified Control.Monad.Reader                            as Reader 
import           Control.Monad.State.Strict                      (MonadState, StateT)
import qualified Control.Monad.State.Strict                      as State
import           Control.Monad.Trans                             (MonadTrans (..)) 
import           Control.Monad.Trans.Maybe                       (MaybeT)
import           Data.Functor                                    (($>), void)
import           Data.Hashable                                   (Hashable)
import           Data.HashMap.Strict                             (HashMap)
import qualified Data.HashMap.Strict                             as HashMap
import           Data.HashSet                                    (HashSet)
import qualified Data.HashSet                                    as HashSet
import qualified Data.Maybe                                      as Maybe

import           GHC.Types.SrcLoc                                (SrcSpan)

import           Language.Fixpoint.Types                         (PPrint, Symbol, Symbolic)
import qualified Language.Fixpoint.Types.PrettyPrint             as Pretty
import           Language.Haskell.Liquid.Constraint.PathCompress
  ( PathTrace
  , PathTraceST
  , UnionMap
  )
import qualified Language.Haskell.Liquid.Constraint.PathCompress as Path
import           Language.Haskell.Liquid.Constraint.UnionFind    (UnionFind, Valued (..))
import qualified Language.Haskell.Liquid.Constraint.UnionFind    as UnionFind
import qualified Language.Haskell.Liquid.GHC.Misc                as GM
import           Language.Haskell.Liquid.Types.AntiUnify
  ( AUTypeRep
  , Polarity
  , Joinable
  )
import qualified Language.Haskell.Liquid.Types.AntiUnify         as AntiUnify
import           Language.Haskell.Liquid.Types.Errors            (TError)
import qualified Language.Haskell.Liquid.Types.Errors            as Liquid
import           Language.Haskell.Liquid.Types.Fresh             (Freshable)
import qualified Language.Haskell.Liquid.Types.Fresh             as Fresh
import qualified Language.Haskell.Liquid.Types.RefType           as Liquid
import qualified Language.Haskell.Liquid.Types.Renaming          as Renaming
import           Language.Haskell.Liquid.Types.RType
  ( QTyCon
  , Reftable
  , RTypeV
  , RTyVar
  , SpecType
  , UTyCon
  )
import qualified Language.Haskell.Liquid.Types.RType             as Liquid

import qualified Text.PrettyPrint.HughesPJ                       as Pretty

data QuotientSubst v c tv r
  = EmptyQuotient
  | ConcreteQuotient !QTyCon
  | BoundQuotient    !(AUTypeRep v c tv r)

data Substitution v c tv r
  = Substitution
      { substitutionTV :: !(UnionMap tv (RTypeV v c tv r))
      , substitutionQV :: !(UnionFind Symbol (QuotientSubst v c tv r))
      }

data SubstResult v c tv r
  = SubstResult
      { freeVars     :: !(HashSet tv)
      , freeQuotVars :: !(HashMap Symbol (RTypeV v c tv r))
      , resultType   :: !(RTypeV v c tv r)
      }

data SubstInsert v c tv r m
  = SubstInsert
      { baseType     :: !(RTypeV v c tv r)
      , alterType    :: !(RTypeV v c tv r -> UnionT v c tv r m (RTypeV v c tv r))
      , insertErrPos :: !SrcSpan
      , insertErrMsg :: !String
      , strengthen   :: !(r -> r -> r)
      }

data InsertResult v c tv r
  = InsertResult
      { updatedSubst :: !(Substitution v c tv r)
      , insertRoot   :: !(RTypeV v c tv r)
      }

data QuotVarInsert v c r m
  = QuotVarInsert
      { unifyMaybeI :: !(UnifyMaybe v c RTyVar r m)
      , unifyBaseI  :: !([RTyVar] -> SpecType -> RTypeV v c RTyVar r -> m (UnionMap RTyVar (RTypeV v c RTyVar r)))
      , quotientVar :: !(Valued Symbol (QuotientSubst v c RTyVar r))
      , errorPosI   :: !SrcSpan
      }

data QuotVarUnify v c r m
  = QuotVarUnify
      { unifyMaybe   :: !(UnifyMaybe v c RTyVar r m)
      , unifyBase    :: !([RTyVar] -> SpecType -> RTypeV v c RTyVar r -> m (UnionMap RTyVar (RTypeV v c RTyVar r)))
      , leftQuotVar  :: !(Valued Symbol (RTypeV v c RTyVar r))
      , rightQuotVar :: !(Valued Symbol (RTypeV v c RTyVar r))
      , errorPos     :: !SrcSpan
      }

data SubstEnv v c tv r m
  = SubstEnv
      { occursErrPos  :: !SrcSpan
      , occursErrMsg  :: !String
      , occursVars    :: !(HashSet tv)
      , unifyQuotient :: [tv] -> SpecType -> RTypeV v c tv r -> m (UnionMap tv (RTypeV v c tv r))
      , unifyTypes    :: UnifyMaybe v c tv r m
      }

data SubstState v c tv r
  = SubstState
      { subst          :: !(Substitution v c tv r)
      , stFreeVars     :: !(HashSet tv)
      , stFreeQuotVars :: !(HashMap Symbol (RTypeV v c tv r))
      , visitedTyVars  :: !(HashMap tv (RTypeV v c tv r))
      }

newtype SubstT v c tv r m a
  = SubstT { runSubstT :: ReaderT (SubstEnv v c tv r m) (StateT (SubstState v c tv r) m) a }
    deriving newtype (Applicative, Functor, Monad)

newtype UnionFindT m a
  = UnionFindT { runUnionFindT :: m a }
    deriving newtype (Applicative, Functor, Monad)

type UnifyMaybe v c tv r m
  =  Polarity
  -> RTypeV v c tv r
  -> RTypeV v c tv r
  -> MaybeT (StateT (Substitution v c tv r) m) (RTypeV v c tv r)

type UnionT v c tv r m = StateT (Substitution v c tv r) m

type SubstType v r = RTypeV v UTyCon RTyVar r

type Substitutable v r t m
  = ( Eq v
    , Freshable m RTyVar
    , Joinable r
    , MonadError (TError t) m
    , PPrint (SubstType v r)
    , PPrint (SubstType v ())
    , Reftable r
    )

instance Hashable tv => Semigroup (Substitution v c tv r) where
  s1 <> s2
    = Substitution
        { substitutionTV = substitutionTV s1 <> substitutionTV s2
        , substitutionQV = substitutionQV s1 <> substitutionQV s2
        }

instance Hashable tv => Monoid (Substitution v c tv r) where
  mempty
    = Substitution
        { substitutionTV = mempty
        , substitutionQV = mempty
        }

instance MonadTrans (SubstT v c tv r) where
  lift = SubstT . Reader.lift . State.lift

instance MonadTrans UnionFindT where
  lift = UnionFindT

instance Monad m => MonadReader (SubstEnv v c tv r m) (SubstT v c tv r m) where
  ask = SubstT Reader.ask

  reader = SubstT . Reader.reader

  local f = SubstT . Reader.local f . runSubstT

instance MonadReader r m => MonadReader r (UnionFindT m) where
  ask = UnionFindT Reader.ask

  reader = UnionFindT . Reader.reader

  local f = UnionFindT . Reader.local f . runUnionFindT

instance Monad m => MonadState (SubstState v c tv r) (SubstT v c tv r m) where
  get = SubstT $ Reader.ReaderT $ const State.get

  put = SubstT . Reader.ReaderT . const . State.put

instance
  MonadState (Substitution v c tv r) m
    => MonadState (UnionFind Symbol (QuotientSubst v c tv r)) (UnionFindT m) where
  get = UnionFindT $ substitutionQV <$> State.get

  put substitutionQV = UnionFindT $ State.modify' \subst -> subst { substitutionQV }

instance MonadError e m => MonadError e (SubstT v c tv r m) where
  throwError = SubstT . Error.throwError

  catchError ma = SubstT . Error.catchError (runSubstT ma) . (runSubstT .)

instance MonadError e m => MonadError e (UnionFindT m) where
  throwError = UnionFindT . Error.throwError

  catchError ma = UnionFindT . Error.catchError (runUnionFindT ma) . (runUnionFindT .)

instance Freshable m a => Freshable (StateT s m) a where
  fresh = State.lift Fresh.fresh

instance Freshable m a => Freshable (SubstT v c tv r m) a where
  fresh = SubstT $ Reader.lift Fresh.fresh

runLiftStateT :: (MonadTrans t, Monad m) => StateT s m a -> s -> t m (a, s)
runLiftStateT k = State.lift . State.runStateT k

insertAll :: (Foldable f, Hashable k) => HashSet k -> f k -> HashSet k
insertAll = foldl' (flip HashSet.insert)

addOccursVarsIn :: (Hashable tv, Monad m) => [tv] -> SubstT v c tv r m a -> SubstT v c tv r m a
addOccursVarsIn αs
  = Reader.local \o@SubstEnv {occursVars} -> o { occursVars = insertAll occursVars αs }

substituteVarsWith
  :: forall v c tv r m.
     (Hashable tv, Monad m, Monoid r)
  => (HashSet tv -> tv -> r -> m (RTypeV v c tv r))
     -- | ^ Type variable traversal
  -> (HashSet Symbol -> RTypeV v c tv r -> Symbol -> r -> m (RTypeV v c tv r))
     -- | ^ Quotient variable traversal
  -> RTypeV v c tv r
  -> m (RTypeV v c tv r)
substituteVarsWith tvf qvf = go HashSet.empty HashSet.empty
  where
    go :: HashSet tv -> HashSet Symbol -> RTypeV v c tv r -> m (RTypeV v c tv r)
    go tvs _ Liquid.RVar {..} = tvf tvs rt_var rt_reft

    go tvs qvs τ@Liquid.RFun {..}
      = makeFun <$> go tvs qvs rt_in <*> go tvs qvs rt_out
        where
          makeFun tin tout
            = τ { Liquid.rt_in  = tin
                , Liquid.rt_out = tout
                }

    go tvs qvs τ@Liquid.RAllT {..}
      = makeAllT <$> traverse (go' tvs qvs) rt_tvbind <*> go tvs' qvs rt_ty
        where
          tvs' = HashSet.insert (Liquid.ty_var_value rt_tvbind) tvs
          makeAllT tvbind ty
            = τ { Liquid.rt_tvbind = tvbind
                , Liquid.rt_ty     = ty
                }

    go tvs qvs τ@Liquid.RAllP {..}
      = makeAllP <$> traverse (go' tvs qvs) rt_pvbind <*> go tvs qvs rt_ty
        where makeAllP pvbind ty = τ { Liquid.rt_pvbind = pvbind, Liquid.rt_ty = ty }

    go tvs qvs τ@Liquid.RChooseQ {..}
      = makeChoose <$> traverse (go' tvs qvs) rt_qvbind <*> go tvs qvs' rt_ty
        where
          Liquid.QVar {..}     = rt_qvbind
          qvs'                 = HashSet.insert qv_quotient $ insertAll qvs qv_quotients
          makeChoose qvbind ty
            = τ { Liquid.rt_qvbind = qvbind
                , Liquid.rt_ty     = ty
                }

    go tvs qvs Liquid.RQuotient {..} = do
      τ <- go tvs qvs rt_ty
      qvf qvs τ rt_quotient rt_reft

    go tvs qvs τ@Liquid.RApp {..}
      = makeApp <$> traverse (go tvs qvs) rt_args <*> traverse (traverse $ go tvs qvs) rt_pargs
        where
          makeApp args pargs
            = τ { Liquid.rt_args  = args
                , Liquid.rt_pargs = pargs
                }

    go tvs qvs τ@Liquid.RAllE {..}
      = makeAllE <$> go tvs qvs rt_allarg <*> go tvs qvs rt_ty
        where makeAllE allarg ty = τ { Liquid.rt_allarg = allarg, Liquid.rt_ty = ty }

    go tvs qvs τ@Liquid.REx {..}
      = makeEx <$> go tvs qvs rt_exarg <*> go tvs qvs rt_ty
        where makeEx exarg ty = τ { Liquid.rt_exarg = exarg, Liquid.rt_ty = ty }

    go _ _ τ@(Liquid.RExprArg _) = pure τ

    go tvs qvs τ@Liquid.RAppTy {..}
      = makeAppTy <$> go tvs qvs rt_arg <*> go tvs qvs rt_res
        where
          makeAppTy arg res
            = τ { Liquid.rt_arg = arg
                , Liquid.rt_res = res
                }

    go tvs qvs τ@Liquid.RRTy {..}
      = makeRTy <$> traverse (traverse $ go tvs qvs) rt_env <*> go tvs qvs rt_ty
        where makeRTy env ty = τ { Liquid.rt_env = env, Liquid.rt_ty = ty }

    go _ _ τ@(Liquid.RHole _) = pure τ

    tvf' tvs tvs' tv _
      = void <$> tvf (HashSet.union tvs tvs') tv mempty

    qvf' qvs qvs' τ q _
      = void <$> qvf (HashSet.union qvs qvs') (τ $> mempty) q mempty

    go' :: HashSet tv -> HashSet Symbol -> RTypeV v c tv r' -> m (RTypeV v c tv ())
    go' tvs qvs = substituteVarsWith (tvf' tvs) (qvf' qvs) . void

unifyFind
  :: Substitutable v r t m => PathTrace RTyVar (SubstType v r) (SubstT v UTyCon RTyVar r m) r
unifyFind
  = Path.PathTrace
      { refineTrace     = flip Liquid.strengthen
      , accumulateTrace = Liquid.meet
      , ..
      }
  where
    baseTrace rt_var = pure Liquid.RVar {rt_var, rt_reft = mempty}

    stepTrace _ Liquid.RVar {..} = pure $ Path.Continue rt_var rt_reft
    stepTrace path τ = State.lift $ Path.Done <$> addOccursVarsIn path (checkOccursSubst τ)

insertVisited :: Hashable tv => tv -> RTypeV v c tv r -> SubstState v c tv r -> SubstState v c tv r
insertVisited α τ st@SubstState {visitedTyVars}
  = st { visitedTyVars = HashMap.insert α τ visitedTyVars }

-- | Memoized lookup for type variables to avoid repeated use of union-find.
lookupVisitedOr
  :: (Hashable tv, Monad m, Reftable r)
  => tv -> r -> SubstT v c tv r m (RTypeV v c tv r) -> SubstT v c tv r m (RTypeV v c tv r)
lookupVisitedOr α r notVisited
  = State.gets (HashMap.lookup α . visitedTyVars) >>= \case
      Just τ  -> pure $ Liquid.strengthen τ r
      Nothing -> do
        τ <- notVisited
        State.modify' (insertVisited α τ) $> Liquid.strengthen τ r

insertIfVar :: Hashable tv => RTypeV v c tv r -> HashSet tv -> HashSet tv
insertIfVar Liquid.RVar {rt_var} = HashSet.insert rt_var
insertIfVar _                    = id

lookupTV :: Substitutable v r t m => RTyVar -> SubstT v UTyCon RTyVar r m (SubstType v r)
lookupTV α = do
  st@SubstState {..} <- State.get
  (τ, σ) <- Path.findWithPath unifyFind α $ substitutionTV subst
  State.put st
    { subst      = subst { substitutionTV = σ }
    , stFreeVars = insertIfVar τ stFreeVars
    } $> τ

lookupTVs
  :: Substitutable v r t m
  => SubstEnv v UTyCon RTyVar r m
  -> [RTyVar]
  -> UnionMap RTyVar (RTypeV v UTyCon RTyVar r)
  -> m [RTypeV v UTyCon RTyVar r]
lookupTVs γ αs substitutionTV
  = State.evalStateT (Reader.runReaderT (runSubstT $ traverse lookupTV αs) γ)
      SubstState
        { subst          = Substitution { substitutionTV, substitutionQV = mempty }
        , stFreeVars     = mempty
        , stFreeQuotVars = mempty
        , visitedTyVars  = mempty
        }

symbolRTyVars :: [Symbol] -> [RTyVar]
symbolRTyVars = map (Liquid.RTV . GM.symbolTyVar)

freshBaseType
  :: forall v c tv r m. (Freshable m tv, Hashable tv, Symbolic tv)
  => [tv]
  -> RTypeV v c tv r
  -> m ([tv], RTypeV v c tv r)
freshBaseType qtvs base = makeFresh <$> traverse (const Fresh.fresh) qtvs
  where
    makeFresh :: [tv] -> ([tv], RTypeV v c tv r)
    makeFresh tvs
      = let renaming = HashMap.fromList $ zip qtvs tvs
            rename v = Maybe.fromMaybe v $ HashMap.lookup v renaming
         in (tvs, Renaming.rename id rename base)

antiUnifyBound
  :: (Eq c, Eq v, Freshable m RTyVar, Joinable r, Monad m)
  => UnifyMaybe v c RTyVar r m
  -> ([RTyVar] -> SpecType -> RTypeV v c RTyVar r -> m (UnionMap RTyVar (RTypeV v c RTyVar r)))
  -> AUTypeRep v c RTyVar r
  -> QuotientSubst v c RTyVar r
  -> StateT (Substitution v c RTyVar r) m (QuotientSubst v c RTyVar r)
antiUnifyBound unify _ τ (BoundQuotient τ') = do
  σ       <- State.get
  (t, σ') <- lift $ State.runStateT (AntiUnify.antiUnifyRepWithM unify τ τ') σ
  State.put σ' $> BoundQuotient t
antiUnifyBound _ unify AntiUnify.AUTypeRep {..} q@(ConcreteQuotient Liquid.QTyCon {qtc_tvs, qtc_base}) = do
  (αs, fbase) <- freshBaseType (symbolRTyVars qtc_tvs) qtc_base
  lift (unify (auTyVars ++ αs) fbase auType) $> q
antiUnifyBound _ _ _ EmptyQuotient = pure EmptyQuotient

doAntiUnify
  :: (Eq c, Eq v, Freshable m RTyVar, Joinable r, MonadError (TError t) m)
  => SrcSpan
  -> UnifyMaybe v c RTyVar r m
  -> ([RTyVar] -> SpecType -> RTypeV v c RTyVar r -> m (UnionMap RTyVar (RTypeV v c RTyVar r)))
  -> QuotientSubst v c RTyVar r
  -> QuotientSubst v c RTyVar r
  -> UnionFindT (StateT (Substitution v c RTyVar r) m) (QuotientSubst v c RTyVar r)
doAntiUnify _   f g (BoundQuotient τ)    q                 = UnionFindT $ antiUnifyBound f g τ q
doAntiUnify _   f g q                    (BoundQuotient τ) = UnionFindT $ antiUnifyBound f g τ q
doAntiUnify _   _ _ EmptyQuotient        _                 = pure EmptyQuotient
doAntiUnify _   _ _ _                    EmptyQuotient     = pure EmptyQuotient
doAntiUnify pos _ _ (ConcreteQuotient q) (ConcreteQuotient q')
  | q == q'   = pure $ ConcreteQuotient q
  | otherwise
      = Error.throwError Liquid.ErrDoesNotUnify
          { leftType  = Pretty.pprint q
          , rightType = Pretty.pprint q'
          , msg       = Pretty.text "Quotient type constructors did not match."
          , pos
          }

lookupQuotient
  :: Substitutable v r t m
  => HashSet Symbol
  -> SubstType v r
  -> Symbol
  -> r
  -> SubstT v UTyCon RTyVar r m (SubstType v r)
lookupQuotient qvs rt_ty rt_quotient rt_reft
  | HashSet.member rt_quotient qvs = pure $ Liquid.RQuotient {..}
  | otherwise = do
      st@SubstState {stFreeQuotVars, subst} <- State.get
      case UnionFind.lookup rt_quotient $ substitutionQV subst of
        Nothing -> pure Liquid.RQuotient {..}
        Just (q :=> BoundQuotient τ) ->
          State.put st
            { stFreeQuotVars = HashMap.insert q (AntiUnify.fromAUTypeRep τ) stFreeQuotVars
            } $> Liquid.RQuotient {rt_quotient = q, ..}
        Just (_ :=> EmptyQuotient) -> pure rt_ty
        Just (_ :=> ConcreteQuotient qtc@Liquid.QTyCon {..}) -> do
          γ@SubstEnv{unifyQuotient} <- Reader.ask
          (αs, fbase)               <- freshBaseType (symbolRTyVars qtc_tvs) qtc_base
          σ                         <- lift $ unifyQuotient αs fbase rt_ty
          rt_args                   <- lift $ lookupTVs γ αs σ
          pure Liquid.RApp
            { rt_tycon = Liquid.QuotientTyCon qtc
            , rt_pargs = []
            , rt_args
            , rt_reft
            }

checkOccursSubst
  :: forall v r t m. Substitutable v r t m
  => SubstType v r -> SubstT v UTyCon RTyVar r m (SubstType v r)
checkOccursSubst τ = substituteVarsWith withVariable lookupQuotient τ
  where
    withVariable tvs rt_var rt_reft
      | HashSet.member rt_var tvs = pure Liquid.RVar {..}
      | otherwise = lookupVisitedOr rt_var rt_reft do
          SubstEnv {..} <- Reader.ask
          if HashSet.member rt_var occursVars then
            Error.throwError Liquid.ErrOccurs
              { pos         = occursErrPos
              , occursLeft  = Pretty.pprint (Liquid.RVar {..} :: SubstType v r)
              , occursRight = Pretty.pprint τ
              , msg         = Pretty.text occursErrMsg
              }
          else lookupTV rt_var

substitute'
  :: forall v r t m. Substitutable v r t m
  => SubstType v r -> SubstT v UTyCon RTyVar r m (SubstType v r)
substitute' = substituteVarsWith withVariable lookupQuotient
  where
    withVariable boundTyVars rt_var rt_reft
      | HashSet.member rt_var boundTyVars = pure Liquid.RVar {..}
      | otherwise = lookupVisitedOr rt_var rt_reft $ lookupTV rt_var

runSubstitution
  :: SubstT v c tv r m a
  -> SubstEnv v c tv r m
  -> SubstState v c tv r
  -> m (a, SubstState v c tv r)
runSubstitution ma = State.runStateT . Reader.runReaderT (runSubstT ma)

makeResult :: (RTypeV v c tv r, SubstState v c tv r) -> SubstResult v c tv r
makeResult (resultType, SubstState {stFreeVars, stFreeQuotVars})
  = SubstResult
      { freeVars     = stFreeVars
      , freeQuotVars = stFreeQuotVars
      , ..
      }

substitute
  :: forall v r t m. Substitutable v r t m
  => SubstEnv v UTyCon RTyVar r m
  -> HashSet RTyVar
  -> Substitution v UTyCon RTyVar r
  -> RTypeV v UTyCon RTyVar r
  -> m (SubstResult v UTyCon RTyVar r)
substitute env stFreeVars subst τ
  = makeResult <$> runSubstitution (substitute' τ) env
      SubstState
        { stFreeQuotVars = HashMap.empty
        , visitedTyVars  = HashMap.empty
        , ..
        }

------------------------------------------------------------------------
-- | Insertion of type and quotient mappings into a substitution map ---
------------------------------------------------------------------------

checkOccursSet
  :: forall v c tv r t m.
     (Hashable tv, MonadError (TError t) m, PPrint (RTypeV v c tv r), PPrint (RTypeV v c tv ()))
  => SrcSpan
  -> String
  -> HashSet tv
  -> RTypeV v c tv r
  -> m ()
checkOccursSet pos errMsg itvs t = maybe (pure ()) Error.throwError $ go itvs t
  where
    go :: PPrint (RTypeV v c tv r') => HashSet tv -> RTypeV v c tv r' -> Maybe (TError t)
    go tvs τ@Liquid.RVar {..}
      | HashSet.member rt_var tvs
          = Just Liquid.ErrOccurs
              { pos
              , occursLeft  = Pretty.pprint τ
              , occursRight = Pretty.pprint t
              , msg         = Pretty.text errMsg
              }
      | otherwise = Nothing

    go tvs Liquid.RFun {..} = go tvs rt_in <|> go tvs rt_out

    go tvs Liquid.RAllT {..}
      = let αs = HashSet.delete (Liquid.ty_var_value rt_tvbind) tvs
         in if HashSet.null αs then Nothing else go αs rt_ty

    go tvs Liquid.RAllP {..} = gos tvs Nothing rt_pvbind

    go tvs Liquid.RChooseQ {..}
      = go tvs (Liquid.qv_type rt_qvbind) <|> go tvs rt_ty

    go tvs Liquid.RQuotient {..} = go tvs rt_ty

    go tvs Liquid.RApp {..}
      = gos tvs (foldl' (\m -> (m <|>) . gos tvs Nothing) Nothing rt_pargs) rt_args

    go tvs Liquid.RAllE {..} = go tvs rt_allarg <|> go tvs rt_ty

    go tvs Liquid.REx {..} = go tvs rt_exarg <|> go tvs rt_ty

    go _ (Liquid.RExprArg _) = Nothing

    go tvs Liquid.RAppTy {..} = go tvs rt_arg <|> go tvs rt_res

    go tvs Liquid.RRTy {..}
      = foldl' (\m -> (m <|>) . go tvs . snd) (go tvs rt_ty) rt_env

    go _ (Liquid.RHole _) = Nothing

    gos
      :: (Foldable f, PPrint (RTypeV v c tv r'))
      => HashSet tv
      -> Maybe (TError t)
      -> f (RTypeV v c tv r')
      -> Maybe (TError t)
    gos tvs = foldl' (\m -> (m <|>) . go tvs)

unifyInsert
  :: (Hashable tv, MonadError (TError t) m, PPrint (RTypeV v c tv r), PPrint (RTypeV v c tv ()))
  => SubstInsert v c tv r m
  -> PathTraceST (UnionFind Symbol (QuotientSubst v c tv r)) tv (RTypeV v c tv r) m r
unifyInsert SubstInsert {..}
  = Path.PathTraceST
      { stepTraceST
      , baseTraceST       = \_ _ -> pure baseType
      , refineTraceST     = flip $ Liquid.strengthenWith strengthen
      , accumulateTraceST = strengthen
      }
  where
    stepTraceST _ Liquid.RVar {..} = pure $ Path.Continue rt_var rt_reft
    stepTraceST path t = checkOccursSet insertErrPos insertErrMsg (HashSet.fromList path) t *> do
      Path.UnionState {..} <- State.get
      (τ, Substitution {..}) <-
        runLiftStateT (alterType t)
          Substitution
            { substitutionTV = unionFindMap
            , substitutionQV = unionState
            }
      State.put Path.UnionState
        { unionState   = substitutionQV
        , unionFindMap = substitutionTV
        } $> Path.Done τ

makeInsertResult
  :: (RTypeV v c tv r, UnionMap tv (RTypeV v c tv r), UnionFind Symbol (QuotientSubst v c tv r))
  -> InsertResult v c tv r
makeInsertResult (insertRoot, substitutionTV, substitutionQV)
  = InsertResult
      { updatedSubst = Substitution { substitutionTV, substitutionQV }
      , ..
      }

insertTypeVarSubst
  :: (Hashable tv, MonadError (TError t) m, PPrint (RTypeV v c tv r), PPrint (RTypeV v c tv ()))
  => tv
  -> SubstInsert v c tv r m
  -> Substitution v c tv r
  -> m (InsertResult v c tv r)
insertTypeVarSubst variable si Substitution{..}
  = makeInsertResult
      <$> Path.insertWithPathST (unifyInsert si) substitutionQV variable substitutionTV

unionQuotientVars
  :: (Eq c, Eq v, Freshable m RTyVar, Joinable r, MonadError (TError t) m)
  => QuotVarUnify v c r m
  -> Substitution v c RTyVar r
  -> m (Substitution v c RTyVar r)
unionQuotientVars QuotVarUnify {..}
  = State.execStateT $ runUnionFindT
      $ UnionFind.union (doAntiUnify errorPos unifyMaybe unifyBase)
          (fmap (BoundQuotient . AntiUnify.toAUTypeRep) leftQuotVar)
          (fmap (BoundQuotient . AntiUnify.toAUTypeRep) rightQuotVar)

addQuotVarSubst
  :: (Eq c, Eq v, Freshable m RTyVar, Joinable r, MonadError (TError t) m)
  => QuotVarInsert v c r m
  -> Substitution v c RTyVar r
  -> m (Substitution v c RTyVar r)
addQuotVarSubst QuotVarInsert {..}
  = State.execStateT $ runUnionFindT
      $ UnionFind.find (doAntiUnify errorPosI unifyMaybeI unifyBaseI) quotientVar
