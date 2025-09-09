{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}

module Language.Haskell.Liquid.Types.AntiUnify
  ( AUTypeRep (..)
  , Polarity  (..)
  , FromInt   (..)
  , Joinable  (..)
  , antiUnify
  , antiUnifyWith
  , antiUnifyWithM
  , antiUnifyRep
  , antiUnifyRepWith
  , antiUnifyRepWithM
  , fromAUTypeRep
  , toAUTypeRep
  , meetOrJoin
  , inverse
  , quotientTyConRep
  ) where

import           Control.Monad                         (replicateM, zipWithM)
import           Control.Monad.State.Strict            (StateT)
import qualified Control.Monad.State.Strict            as State
import           Control.Monad.Trans.Maybe             (MaybeT)
import qualified Control.Monad.Trans.Maybe             as Maybe
import           Data.Functor                          (($>))
import           Data.Functor.Classes                  (liftEq)
import qualified Data.Functor.Identity                 as Identity

import           Data.Hashable                         (Hashable)
import           Data.HashMap.Internal                 (Hash)
import qualified Data.HashMap.Internal                 as HashMapI
import           Data.HashMap.Strict                   (HashMap)
import qualified Data.HashMap.Strict                   as HashMap

import           Language.Fixpoint.Types               (Symbol)
import qualified Language.Fixpoint.Types               as Fixpoint
import qualified Language.Haskell.Liquid.GHC.Misc      as GM
import           Language.Haskell.Liquid.Types.RType
  ( BTyVar
  , QTyCon
  , RReft
  , RTyCon
  , RTyVar
  , RTypeV
  , Reftable
  )
import qualified Language.Haskell.Liquid.Types.RType   as Liquid

data AntiUnifyState v c tv r
  = AntiUnifyState
      { freshTypeVarCount :: !Int
      , freshTypeVars     :: ![tv]
      , substitutionsL    :: !(HashMap tv [(RTypeV v c tv r, RTypeV v c tv r)])
      , substitutionsR    :: !(HashMap tv [(RTypeV v c tv r, RTypeV v c tv r)])
      }

data AUTypeRep v c tv r
  = AUTypeRep
      { auTyVars :: ![tv]
        -- | The type variables that are unifiable in `aVarType`.
      , auType   :: !(RTypeV v c tv r)
        -- | The underlying type.
      }
    deriving (Foldable, Functor, Traversable)

data Polarity = Positive | Negative

-- | Types whose elements can be constructed from an integer.
class FromInt a where
  fromInt :: Int -> a

-- | Additional join monoid structure for lattice-like Reftables.
class Reftable r => Joinable r where
  join :: r -> r -> r

instance FromInt Symbol where
  fromInt = Fixpoint.tempSymbol "u" . toInteger

instance FromInt RTyVar where
  fromInt = Liquid.RTV . GM.symbolTyVar . Fixpoint.tempSymbol "u" . toInteger

instance FromInt BTyVar where
  fromInt = Liquid.BTV . Fixpoint.dummyLoc . Fixpoint.tempSymbol "u" . toInteger

instance Joinable () where
  join _ _ = ()

findFirst :: (k -> Bool) -> [(k, v)] -> Maybe v
findFirst p = go
  where
    go [] = Nothing
    go ((k, v) : kvs)
      | p k       = Just v
      | otherwise = go kvs

zipWithAndThenM :: Applicative m => (a -> b -> m c) -> m c -> [a] -> [b] -> m [c]
zipWithAndThenM _ _ []       []       = pure []
zipWithAndThenM _ z []       bs       = replicateM (length bs) z
zipWithAndThenM _ z as       []       = replicateM (length as) z
zipWithAndThenM f z (a : as) (b : bs) = (:) <$> f a b <*> zipWithAndThenM f z as bs

inverse :: Polarity -> Polarity
inverse Positive = Negative
inverse Negative = Positive

meetOrJoin :: Joinable r => Polarity -> r -> r -> r
meetOrJoin Positive = Liquid.meet
meetOrJoin Negative = join

allT :: Monoid r => RTypeV v c tv r -> tv -> RTypeV v c tv r
allT rt_ty ty_var_value
  = Liquid.RAllT
      { rt_tvbind
          = Liquid.RTVar
              { ty_var_value
              , ty_var_info = Liquid.RTVNoInfo False
              }
      , rt_ty
      , rt_ref = mempty
      }

fromAUTypeRep :: Monoid r => AUTypeRep v c tv r -> RTypeV v c tv r
fromAUTypeRep AUTypeRep {..} = foldl' allT auType auTyVars

toAUTypeRep :: RTypeV v c tv r -> AUTypeRep v c tv r
toAUTypeRep = uncurry AUTypeRep . go []
  where
    go tvs Liquid.RAllT {rt_tvbind, rt_ty} = go (Liquid.ty_var_value rt_tvbind : tvs) rt_ty
    go tvs τ                               = (tvs, τ)

quotientTyConRep :: QTyCon -> AUTypeRep Symbol RTyCon RTyVar RReft
quotientTyConRep Liquid.QTyCon {qtc_tvs, qtc_base}
  = AUTypeRep
      { auTyVars = map (Liquid.RTV . GM.symbolTyVar) qtc_tvs
      , auType   = qtc_base
      }

auRigid :: Polarity -> RTypeV v c tv r -> RTypeV v c tv r -> Maybe (RTypeV v c tv r)
auRigid _ _ _ = Nothing

initialAUState :: AntiUnifyState v c tv r
initialAUState
  = AntiUnifyState
      { freshTypeVarCount = 0
      , freshTypeVars     = []
      , substitutionsL    = HashMap.empty
      , substitutionsR    = HashMap.empty
      }

freshTypeVar
  :: (FromInt tv, Monoid r, Monad m) => StateT (AntiUnifyState v c tv r) m (RTypeV v c tv r)
freshTypeVar
  = State.state \st@AntiUnifyState{freshTypeVarCount, freshTypeVars} ->
      let rt_var = fromInt freshTypeVarCount
       in ( Liquid.RVar
              { rt_var
              , rt_reft = mempty
              }
          , st
              { freshTypeVarCount = freshTypeVarCount + 1
              , freshTypeVars     = rt_var : freshTypeVars
              }
          )

equalShapes :: (Eq c, Eq v, Eq tv) => RTypeV v c tv r -> RTypeV v c tv r -> Bool
equalShapes Liquid.RVar {rt_var} Liquid.RVar {rt_var = rt_var'} = rt_var == rt_var'

equalShapes Liquid.RFun {rt_in, rt_out} Liquid.RFun {rt_in = rt_in', rt_out = rt_out'}
  = equalShapes rt_in rt_in' && equalShapes rt_out rt_out'

equalShapes Liquid.RAllT {rt_tvbind, rt_ty} Liquid.RAllT {rt_tvbind = rt_tvbind', rt_ty = rt_ty'}
  | rt_tvbind == rt_tvbind' = equalShapes rt_ty rt_ty'

equalShapes Liquid.RAllP {rt_pvbind, rt_ty} Liquid.RAllP {rt_pvbind = rt_pvbind', rt_ty = rt_ty'}
  | rt_pvbind == rt_pvbind' = equalShapes rt_ty rt_ty'

equalShapes Liquid.RChooseQ {rt_qvbind, rt_ty} Liquid.RChooseQ {rt_qvbind = rt_qvbind', rt_ty = rt_ty'}
  | rt_qvbind == rt_qvbind' = equalShapes rt_ty rt_ty'

equalShapes Liquid.RQuotient {rt_ty} Liquid.RQuotient {rt_ty = rt_ty'} = equalShapes rt_ty rt_ty'

equalShapes Liquid.RApp {rt_tycon, rt_args} Liquid.RApp {rt_tycon = rt_tycon', rt_args = rt_args'}
  | rt_tycon == rt_tycon' = liftEq equalShapes rt_args rt_args'

equalShapes Liquid.RAllE {rt_allarg, rt_ty} Liquid.RAllE {rt_allarg = rt_allarg', rt_ty = rt_ty'}
  = equalShapes rt_allarg rt_allarg' && equalShapes rt_ty rt_ty'

equalShapes Liquid.REx {rt_exarg, rt_ty} Liquid.REx {rt_exarg = rt_exarg', rt_ty = rt_ty'}
  = equalShapes rt_exarg rt_exarg' && equalShapes rt_ty rt_ty'

equalShapes (Liquid.RExprArg e) (Liquid.RExprArg e') = e == e'

equalShapes Liquid.RAppTy {rt_arg, rt_res} Liquid.RAppTy {rt_arg = rt_arg', rt_res = rt_res'}
  = equalShapes rt_arg rt_arg' && equalShapes rt_res rt_res'

equalShapes Liquid.RRTy {rt_env, rt_ty} Liquid.RRTy {rt_env = rt_env', rt_ty = rt_ty'}
  = liftEq equalSub rt_env rt_env' && equalShapes rt_ty rt_ty'
    where
      equalSub (sL, tL) (sR, tR) = sL == sR && equalShapes tL tR

equalShapes Liquid.RHole {} Liquid.RHole {} = True

equalShapes _ _ = False

isTypeVar :: Eq tv => tv -> RTypeV v c tv r -> Bool
isTypeVar α Liquid.RVar {rt_var} = α == rt_var
isTypeVar _ _                    = False

lookupSubstTy
  :: (Eq c, Eq v, Eq tv)
  => Hash
  -> tv
  -> RTypeV v c tv r
  -> HashMap tv [(RTypeV v c tv r, RTypeV v c tv r)]
  -> Either [(RTypeV v c tv r, RTypeV v c tv r)] (RTypeV v c tv r)
lookupSubstTy h α τ m = case HashMapI.lookup' h α m of
  Nothing  -> Left []
  Just !σs -> case findFirst (`equalShapes` τ) σs of
    Nothing -> Left σs
    Just τ' -> Right τ'

lookupSubstTV
  :: Eq tv
  => Hash
  -> tv
  -> tv
  -> HashMap tv [(RTypeV v c tv r, RTypeV v c tv r)]
  -> Either [(RTypeV v c tv r, RTypeV v c tv r)] (RTypeV v c tv r)
lookupSubstTV h αL αR m = case HashMapI.lookup' h αL m of
  Nothing  -> Left []
  Just !σs -> case findFirst (isTypeVar αR) σs of
    Nothing -> Left σs
    Just τ' -> Right τ'

insertOrCons :: Monoid r => tv -> t -> Maybe [(RTypeV v c tv r, t)] -> [(RTypeV v c tv r, t)]
insertOrCons α τ = maybe [(Liquid.RVar α mempty, τ)] ((Liquid.RVar α mempty, τ):)

addSubstitutionL
  :: (Eq c, Eq v, FromInt tv, Hashable tv, Monoid r, Monad m)
  => tv -> RTypeV v c tv r -> StateT (AntiUnifyState v c tv r) m (RTypeV v c tv r)
addSubstitutionL α τ = do
  st@AntiUnifyState {freshTypeVarCount, freshTypeVars, substitutionsL} <- State.get
  let h = HashMapI.hash α
  case lookupSubstTy h α τ substitutionsL of
    Left !σs ->
      let ftvar   = fromInt freshTypeVarCount
          ftvarT  = Liquid.RVar ftvar mempty
       in State.put st
            { freshTypeVarCount = freshTypeVarCount + 1
            , freshTypeVars     = ftvar : freshTypeVars
            , substitutionsL    = HashMapI.insert' h α ((τ, ftvarT) : σs) substitutionsL
            } $> ftvarT
    Right !τ' -> pure τ'

addSubstitutionR
  :: (Eq c, Eq v, FromInt tv, Hashable tv, Monoid r, Monad m)
  => tv -> RTypeV v c tv r -> StateT (AntiUnifyState v c tv r) m (RTypeV v c tv r)
addSubstitutionR α τ = do
  st@AntiUnifyState {freshTypeVarCount, freshTypeVars, substitutionsR} <- State.get
  let h = HashMapI.hash α
  case lookupSubstTy h α τ substitutionsR of
    Left !σs ->
      let ftvar   = fromInt freshTypeVarCount
          ftvarT  = Liquid.RVar ftvar mempty
       in State.put st
            { freshTypeVarCount = freshTypeVarCount + 1
            , freshTypeVars     = ftvar : freshTypeVars
            , substitutionsR    = HashMapI.insert' h α ((τ, ftvarT) : σs) substitutionsR
            } $> ftvarT
    Right !τ' -> pure τ'

addSubstitutionLR
  :: (FromInt tv, Hashable tv, Monoid r, Monad m)
  => tv -> tv -> StateT (AntiUnifyState v c tv r) m (RTypeV v c tv r)
addSubstitutionLR αL αR = do
  st@AntiUnifyState {..} <- State.get
  let h = HashMapI.hash αL
  case lookupSubstTV h αL αR substitutionsL of
    Left  !σs ->
      let ftvar   = fromInt freshTypeVarCount
          ftvarT  = Liquid.RVar ftvar mempty
       in State.put st
            { freshTypeVarCount = freshTypeVarCount + 1
            , freshTypeVars     = ftvar : freshTypeVars
            , substitutionsL    = HashMapI.insert' h αL ((Liquid.RVar αR mempty, ftvarT) : σs) substitutionsL
            , substitutionsR    = HashMap.alter (Just . insertOrCons αL ftvarT) αR substitutionsR
            } $> ftvarT
    Right !τ' -> pure τ'

freshOrStrengthen
  :: (Monad m, FromInt tv, Joinable r)
  => MaybeT m (RTypeV v c tv r)
  -> StateT (AntiUnifyState v c tv r) m (RTypeV v c tv r)
freshOrStrengthen (Maybe.MaybeT lookupAt) = State.lift lookupAt >>= maybe freshTypeVar pure

antiUnifyST
  :: (Eq c, Eq v, FromInt tv, Hashable tv, Joinable r, Monad m)
  => (Polarity -> RTypeV v c tv r -> RTypeV v c tv r -> MaybeT m (RTypeV v c tv r))
  -> AUTypeRep v c tv r
  -> AUTypeRep v c tv r
  -> StateT (AntiUnifyState v c tv r) m (RTypeV v c tv r)
antiUnifyST unify
  AUTypeRep {auTyVars = tvsL, auType = t}
  AUTypeRep {auTyVars = tvsR, auType = u} = go Negative t u
  where
    go p τ@Liquid.RVar {..} τ'@Liquid.RVar {rt_var = rt_var', rt_reft = rt_reft'}
      | rt_var `elem` tvsL
          = if rt_var' `elem` tvsR
              then addSubstitutionLR rt_var rt_var'
              else addSubstitutionL rt_var τ'
      | rt_var' `elem` tvsR = addSubstitutionR rt_var' τ
      | rt_var == rt_var'   = pure τ { Liquid.rt_reft = meetOrJoin p rt_reft rt_reft' }

    go _ Liquid.RVar {..} τ'
      | rt_var `elem` tvsL = addSubstitutionL rt_var τ'

    go _ τ Liquid.RVar {..}
      | rt_var `elem` tvsR = addSubstitutionR rt_var τ

    go p τ@Liquid.RFun {rt_in, rt_out, rt_reft}
           Liquid.RFun {rt_in = rt_in', rt_out = rt_out', rt_reft = rt_reft'}
      = makeFun <$> go (inverse p) rt_in rt_in' <*> go p rt_out rt_out'
        where
          makeFun tin tout
            = τ { Liquid.rt_in   = tin
                , Liquid.rt_out  = tout
                , Liquid.rt_reft = meetOrJoin p rt_reft rt_reft'
                }

    go p τ@Liquid.RAllT {rt_tvbind, rt_ty, rt_ref}
           Liquid.RAllT {rt_tvbind = rt_tvbind', rt_ty = rt_ty', rt_ref = rt_ref'}
      | rt_tvbind == rt_tvbind' = makeAllT <$> go p rt_ty rt_ty'
        where makeAllT ty = τ { Liquid.rt_ty = ty, Liquid.rt_ref = meetOrJoin p rt_ref rt_ref' }

    go p τ@Liquid.RAllP {rt_pvbind, rt_ty}
           Liquid.RAllP {rt_pvbind = rt_pvbind', rt_ty = rt_ty'}
      | rt_pvbind == rt_pvbind' = makeAllP <$> go p rt_ty rt_ty'
        where makeAllP ty = τ { Liquid.rt_ty = ty }

    go p τ@Liquid.RChooseQ {rt_qvbind, rt_ty, rt_reft}
           Liquid.RChooseQ {rt_qvbind = rt_qvbind', rt_ty = rt_ty', rt_reft = rt_reft'}
      | rt_qvbind == rt_qvbind' = makeChoose <$> go p rt_ty rt_ty'
        where
          makeChoose ty
            = τ { Liquid.rt_ty   = ty
                , Liquid.rt_reft = meetOrJoin p rt_reft rt_reft'
                }

    go p τ@Liquid.RQuotient {rt_ty, rt_quotient, rt_reft}
           Liquid.RQuotient {rt_ty = rt_ty', rt_quotient = rt_quotient', rt_reft = rt_reft'}
      | rt_quotient == rt_quotient' = makeQuotient <$> go p rt_ty rt_ty'
        where
          makeQuotient ty
            = τ { Liquid.rt_ty   = ty
                , Liquid.rt_reft = meetOrJoin p rt_reft rt_reft'
                }

    go p τ@Liquid.RApp {rt_tycon, rt_args, rt_reft}
           Liquid.RApp {rt_tycon = rt_tycon', rt_args = rt_args', rt_reft = rt_reft'}
      | rt_tycon == rt_tycon'
          = makeApp <$> zipWithAndThenM (go p) freshTypeVar rt_args rt_args'
        where
          makeApp args
            = τ { Liquid.rt_args  = args
                , Liquid.rt_reft  = meetOrJoin p rt_reft rt_reft'
                }

    go p τ@Liquid.RAllE {rt_bind, rt_allarg, rt_ty}
           Liquid.RAllE {rt_bind = rt_bind', rt_allarg = rt_allarg', rt_ty = rt_ty'}
      | rt_bind == rt_bind'
          = makeAllE <$> go (inverse p) rt_allarg rt_allarg' <*> go p rt_ty rt_ty'
        where makeAllE allarg ty = τ { Liquid.rt_allarg = allarg, Liquid.rt_ty = ty }

    go p τ@Liquid.REx {rt_bind, rt_exarg, rt_ty}
           Liquid.REx {rt_bind = rt_bind', rt_exarg = rt_exarg', rt_ty = rt_ty'}
      | rt_bind == rt_bind'
          = makeEx <$> go (inverse p) rt_exarg rt_exarg' <*> go p rt_ty rt_ty'
        where makeEx exarg ty = τ { Liquid.rt_exarg = exarg, Liquid.rt_ty = ty }

    go _ (Liquid.RExprArg e) (Liquid.RExprArg e')
      | e == e' = pure $ Liquid.RExprArg e

    go p τ@Liquid.RAppTy {rt_arg, rt_res, rt_reft}
           Liquid.RAppTy {rt_arg = rt_arg', rt_res = rt_res', rt_reft = rt_reft'}
      = makeAppTy <$> go p rt_arg rt_arg' <*> go p rt_res rt_res'
        where
          makeAppTy arg res
            = τ { Liquid.rt_arg  = arg
                , Liquid.rt_res  = res
                , Liquid.rt_reft = meetOrJoin p rt_reft rt_reft'
                }

    go p τ@Liquid.RRTy {rt_env, rt_ty, rt_ref}
           Liquid.RRTy {rt_env = rt_env', rt_ty = rt_ty', rt_ref = rt_ref'}
      | length rt_env == length rt_env'
          = makeRTy <$> zipWithM makeBind rt_env rt_env' <*> go p rt_ty rt_ty'
        where
          makeRTy env ty
            = τ { Liquid.rt_env = env
                , Liquid.rt_ty  = ty
                , Liquid.rt_ref = meetOrJoin p rt_ref rt_ref'
                }

          makeBind (sL, tL) (sR, tR)
            | sL == sR  = (sL,) <$> go p tL tR
            | otherwise = (sL,) <$> freshTypeVar

    go p (Liquid.RHole r) (Liquid.RHole r') = pure $ Liquid.RHole $ meetOrJoin p r r'

    go p τ τ' = freshOrStrengthen $ unify p τ τ'

antiUnifyRepWithM
  :: (Eq c, Eq v, FromInt tv, Hashable tv, Joinable r, Monad m)
  => (Polarity -> RTypeV v c tv r -> RTypeV v c tv r -> MaybeT m (RTypeV v c tv r))
  -> AUTypeRep v c tv r
  -> AUTypeRep v c tv r
  -> m (AUTypeRep v c tv r)
antiUnifyRepWithM unify t u
  = makeResult <$> State.runStateT (antiUnifyST unify t u) initialAUState
    where
      makeResult (auType, AntiUnifyState {freshTypeVars})
        = AUTypeRep { auTyVars = freshTypeVars, auType }

antiUnifyRepWith
  :: (Eq c, Eq v, FromInt tv, Hashable tv, Joinable r)
  => (Polarity -> RTypeV v c tv r -> RTypeV v c tv r -> Maybe (RTypeV v c tv r))
  -> AUTypeRep v c tv r
  -> AUTypeRep v c tv r
  -> AUTypeRep v c tv r
antiUnifyRepWith unify t
  = Identity.runIdentity . antiUnifyRepWithM (\p τ -> Maybe.hoistMaybe . unify p τ) t

antiUnifyRep
  :: (Eq c, Eq v, FromInt tv, Hashable tv, Joinable r)
  => AUTypeRep v c tv r -> AUTypeRep v c tv r -> AUTypeRep v c tv r
antiUnifyRep = antiUnifyRepWith auRigid

antiUnifyWithM
  :: (Eq c, Eq v, FromInt tv, Hashable tv, Joinable r, Monad m)
  => (Polarity -> RTypeV v c tv r -> RTypeV v c tv r -> MaybeT m (RTypeV v c tv r))
  -> RTypeV v c tv r
  -> RTypeV v c tv r
  -> m (RTypeV v c tv r)
antiUnifyWithM unify t u
  = makeResult <$> State.runStateT (antiUnifyST unify at au) initialAUState
    where
      at = toAUTypeRep t
      au = toAUTypeRep u

      makeResult (auType, AntiUnifyState {freshTypeVars}) = foldl' allT auType freshTypeVars

antiUnifyWith
  :: (Eq c, Eq v, FromInt tv, Hashable tv, Joinable r)
  => (Polarity -> RTypeV v c tv r -> RTypeV v c tv r -> Maybe (RTypeV v c tv r))
  -> RTypeV v c tv r
  -> RTypeV v c tv r
  -> RTypeV v c tv r
antiUnifyWith unify t
  = Identity.runIdentity . antiUnifyWithM (\p τ -> Maybe.hoistMaybe . unify p τ) t

antiUnify
  :: (Eq c, Eq v, FromInt tv, Hashable tv, Joinable r)
  => RTypeV v c tv r -> RTypeV v c tv r -> RTypeV v c tv r
antiUnify = antiUnifyWith auRigid
