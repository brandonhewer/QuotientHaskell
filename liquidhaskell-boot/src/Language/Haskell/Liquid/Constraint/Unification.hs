{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE BlockArguments        #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE UndecidableInstances  #-}

-- | First-order unification for refinement types.

module Language.Haskell.Liquid.Constraint.Unification
  ( UnifyResult  (..)
  , UnifySession
  , UnifyTypeRep (..)
  , addTypeVarToSession
  , applyUnifySession
  , fromUnifyTypeRep
  , toUnifyTypeRep
  , unifyInSession
  , unifyRepWithType
  , unifyTypeRepVar
  ) where

import           Control.Monad                                   (zipWithM)
import           Control.Monad.Except                            (MonadError)
import qualified Control.Monad.Except                            as Error
import           Control.Monad.State.Strict                      (StateT)
import qualified Control.Monad.State.Strict                      as State
import           Data.Foldable                                   (foldrM)
import           Data.Functor                                    (($>), void)
import           Data.Hashable                                   (Hashable)
import qualified Data.HashMap.Internal                           as HashMapI
import           Data.HashMap.Strict                             (HashMap)
import qualified Data.HashMap.Strict                             as HashMap
import           Data.HashSet                                    (HashSet)
import qualified Data.HashSet                                    as HashSet
import qualified Data.Maybe                                      as Maybe

import           GHC.Types.SrcLoc                                (SrcSpan)

import           Language.Fixpoint.Types                         (Expr, PPrint, Symbol)
import qualified Language.Fixpoint.Types                         as Fixpoint
import qualified Language.Fixpoint.Types.PrettyPrint             as Pretty
import qualified Language.Haskell.Liquid.Constraint.PathCompress as Path
import qualified Language.Haskell.Liquid.Constraint.Substitution as Substitution
import           Language.Haskell.Liquid.Constraint.Substitution
  ( Substitution (..)
  , SubstInsert
  , UnifyMaybe
  )
import           Language.Haskell.Liquid.Constraint.UnionFind    (Valued (..))
import           Language.Haskell.Liquid.Types.AntiUnify
  ( AUTypeRep
  , FromInt
  , Joinable
  , Polarity
  )
import qualified Language.Haskell.Liquid.Types.AntiUnify         as Liquid
import qualified Language.Haskell.Liquid.Types.QuotSubst         as Quotient
import           Language.Haskell.Liquid.Types.RefType           (FreeVar)
import qualified Language.Haskell.Liquid.Types.RefType           as Liquid
import           Language.Haskell.Liquid.Types.RType
    ( PVar
    , QVU
    , RSort
    , RTProp
    , RTVar
    , RTVInfo
    , RType
    , RTypeV
    , RTyVar
    , SpecQVar
    , TyConable
    , RTyCon
    )
import qualified Language.Haskell.Liquid.Types.RType             as Liquid
import qualified Language.Haskell.Liquid.Types.RTypeOp           as Liquid
import           Language.Haskell.Liquid.Types.Errors            (TError)
import qualified Language.Haskell.Liquid.Types.Errors            as Liquid
import           Language.Haskell.Liquid.Types.Types             (SubsTy)

import qualified Text.PrettyPrint.HughesPJ                       as Pretty

data UnifyTypeRep r
  = UnifyTypeRep
      { repBase      :: !(RType RTyCon RTyVar r)
      , repTypeVars  :: ![(RTVar RTyVar RSort, r)]
      , repPredVars  :: ![PVar RSort]
      , repQuotVars  :: ![(SpecQVar, r)]
      , repUnifiable :: !(HashMap RTyVar RTyVar)
      , repQuotTypes :: !(HashMap Symbol (AUTypeRep Symbol RTyCon RTyVar r))
      , repFVCount   :: !Int
      , repQVCount   :: !Int
      }

data UnificationEnv
  = UnificationEnv
      { unifiableVars  :: !(HashMap RTyVar RTyVar)
      , unPolarity     :: !Polarity
      , errMsg         :: !String
      , errPos         :: !SrcSpan
      }

type UnificationState r = Substitution Symbol RTyCon RTyVar r

data UnifySession c tv r
  = UnifySession
      { unSubstitution :: !(HashMap tv (RType c tv r))
      , unUnifiable    :: !(HashMap tv tv)
      }

data UnifyResult c tv r
  = UnifyResult
      { unSession  :: !(UnifySession c tv r)
      , unSkeleton :: !(RType c tv r)
      }

type Unifiable r t m
  = ( Hashable RTyVar
    , Joinable r
    , MonadError (TError t) m
    )

maybeA :: Applicative f => b -> (a -> f b) -> Maybe a -> f b
maybeA = maybe . pure

zipWithExactOr :: Applicative f => (a -> b -> f c) -> f [c] -> [a] -> [b] -> f [c]
zipWithExactOr _ _   []       []       = pure []
zipWithExactOr _ err []       _        = err
zipWithExactOr _ err _        []       = err
zipWithExactOr f err (a : as) (b : bs) = (:) <$> f a b <*> zipWithExactOr f err as bs

deleteAll :: (Foldable f, Hashable k) => HashMap k v -> f k -> HashMap k v
deleteAll = foldl' (flip HashMap.delete)

insertWithA
  :: (Applicative f, Hashable k)
  => (v -> v -> f v)
  -> k
  -> v
  -> HashMap k v
  -> f (HashMap k v)
insertWithA f !k !v !m
  = let !h = HashMapI.hash k
     in case HashMapI.lookup' h k m of
          Nothing  -> pure $ HashMapI.insert' h k v m
          Just !v' -> flip (HashMapI.insert' h k) m <$> f v v'
{-# INLINABLE [0] insertWithA #-}

addSubstitution
  :: MonadError (TError t) m
  => RTyVar
  -> SubstInsert Symbol RTyCon RTyVar r (StateT (UnificationState r) m)
  -> StateT (UnificationState r) m (RType RTyCon RTyVar r)
addSubstitution variable ui = do
  σ <- State.get
  Substitution.InsertResult {..} <- Substitution.insertTypeVarSubst variable ui σ
  State.put updatedSubst $> insertRoot

unifyMonotypesMaybe
  :: forall r t m. Unifiable r t m
  => UnificationEnv
  -> RType RTyCon RTyVar r
  -> RType RTyCon RTyVar r
  -> StateT (UnificationState r) m (Maybe (RType RTyCon RTyVar r))
unifyMonotypesMaybe γ τ τ'
  = (Just <$> unifyMonotypes γ τ τ') `Error.catchError` \_ -> pure Nothing

unifyMonotypes
  :: forall r t m. Unifiable r t m
  => UnificationEnv
  -> RType RTyCon RTyVar r
  -> RType RTyCon RTyVar r
  -> StateT (UnificationState r) m (RType RTyCon RTyVar r)
unifyMonotypes γ@UnificationEnv {..} = go unPolarity
  where
    go
      :: Joinable r'
      => Polarity
      -> RType RTyCon RTyVar r'
      -> RType RTyCon RTyVar r'
      -> StateT (UnificationState r') m (RType RTyCon RTyVar r')
    go p τ@Liquid.RVar {..} τ'@Liquid.RVar { rt_var = rt_var', rt_reft = rt_reft' }
      | rt_var == rt_var' = pure $ Liquid.RVar rt_var $ Liquid.meetOrJoin p rt_reft rt_reft'
      | HashMap.member rt_var unifiableVars  = applySubstitution p rt_var rt_reft τ'
      | HashMap.member rt_var' unifiableVars = applySubstitution p rt_var' rt_reft' τ
      | otherwise
          = Error.throwError Liquid.ErrDoesNotUnify
              { pos       = errPos
              , msg       = Pretty.text errMsg
              , leftType  = Pretty.pprint τ
              , rightType = Pretty.pprint τ'
              }

    go p Liquid.RVar {..} τ
      | HashMap.member rt_var unifiableVars = applySubstitution p rt_var rt_reft τ

    go p τ Liquid.RVar {..}
      | HashMap.member rt_var unifiableVars = applySubstitution p rt_var rt_reft τ

    go p   Liquid.RFun {..}
         τ@Liquid.RFun {rt_in = rt_in', rt_out = rt_out', rt_reft = rt_reft'}
      = makeFun <$> go (Liquid.inverse p) rt_in rt_in' <*> go p rt_out rt_out'
        where
          makeFun urt_in urt_out
            = τ { Liquid.rt_in   = urt_in
                , Liquid.rt_out  = urt_out
                , Liquid.rt_reft = Liquid.meetOrJoin p rt_reft rt_reft'
                }

    go p Liquid.RAllT {..}
         Liquid.RAllT {rt_tvbind = rt_tvbind', rt_ty = rt_ty', rt_ref = rt_ref'}
      = makeAllT
          <$> goTVInfo (Liquid.ty_var_info rt_tvbind) (Liquid.ty_var_info rt_tvbind')
          <*> unifyMonotypes γ
                { unPolarity    = p
                , unifiableVars = HashMap.delete (Liquid.ty_var_value rt_tvbind) unifiableVars
                } rt_ty substy
        where
          substy
            = Liquid.subsTyVarMeet'
                ( Liquid.ty_var_value rt_tvbind
                , Liquid.RVar (Liquid.ty_var_value rt_tvbind') mempty
                ) rt_ty'

          makeAllT ty_var_info urt_ty
            = Liquid.RAllT
                { rt_tvbind
                    = Liquid.RTVar
                        { ty_var_value = Liquid.ty_var_value rt_tvbind
                        , ty_var_info
                        }
                , rt_ty  = urt_ty
                , rt_ref = Liquid.meetOrJoin p rt_ref rt_ref'
                }

    go p Liquid.RAllP {..}
         Liquid.RAllP {rt_pvbind = rt_pvbind', rt_ty = rt_ty'}
      = Liquid.RAllP <$> goPVars rt_pvbind rt_pvbind' <*> go p rt_ty rt_ty'

    go p τ@Liquid.RChooseQ {..}
         u@Liquid.RChooseQ {rt_qvbind = rt_qvbind', rt_ty = rt_ty', rt_reft = rt_reft'}
      = makeChoose <$> goQVBinds τ u rt_qvbind rt_qvbind' <*> go p rt_ty rt_ty'
      where
        makeChoose qvbind ty
          = Liquid.RChooseQ
              { rt_qvbind = qvbind
              , rt_ty     = ty
              , rt_reft   = Liquid.meetOrJoin p rt_reft rt_reft'
              }

    go p   Liquid.RQuotient {..}
         τ@Liquid.RQuotient {rt_ty = rt_ty', rt_quotient = rt_quotient', rt_reft = rt_reft'} = do
      σ  <- State.get
      σ' <-
        Substitution.unionQuotientVars
          Substitution.QuotVarUnify
            { unifyMaybe   = doUnifyMaybe
            , unifyBase    = x
            , leftQuotVar  = rt_quotient  :=> rt_ty
            , rightQuotVar = rt_quotient' :=> rt_ty'
            , errorPos     = errPos
            } σ
      State.put σ' *> makeQuotient <$> go p rt_ty rt_ty'
      where
        makeQuotient ty
          = τ { Liquid.rt_ty   = ty
              , Liquid.rt_reft = Liquid.meetOrJoin p rt_reft rt_reft'
              }

    go p Liquid.RQuotient {..} τ = goQuotient p rt_ty rt_quotient rt_reft τ 

    go p τ Liquid.RQuotient {..} = goQuotient p rt_ty rt_quotient rt_reft τ 

    go p τ@Liquid.RApp {..}
         u@Liquid.RApp {rt_tycon = tycon, rt_args = args, rt_pargs = pargs, rt_reft = reft}
      | rt_tycon == tycon
          = makeApp
              <$> zipWithExactOr (go p) didNotUnify rt_args args
              <*> zipWithExactOr goPArgs didNotUnify rt_pargs pargs
      where
        makeApp uargs upargs
          = τ { Liquid.rt_args  = uargs
              , Liquid.rt_pargs = upargs
              , Liquid.rt_reft  = Liquid.meetOrJoin p rt_reft reft
              }

        didNotUnify :: forall s a. StateT s m a
        didNotUnify
          = Error.throwError Liquid.ErrDoesNotUnify
              { pos       = errPos
              , msg       = Pretty.text errMsg
              , leftType  = Pretty.pprint τ
              , rightType = Pretty.pprint u
              }

    go p Liquid.RAllE {..}
         Liquid.RAllE {rt_bind = rt_bind', rt_allarg = rt_allarg', rt_ty = rt_ty'}
      | rt_bind == rt_bind'
          = Liquid.RAllE rt_bind
              <$> go p rt_allarg rt_allarg'
              <*> go p rt_ty rt_ty'

    go p Liquid.REx {..}
         Liquid.REx {rt_bind = rt_bind', rt_exarg = rt_allarg', rt_ty = rt_ty'}
      | rt_bind == rt_bind'
          = Liquid.RAllE rt_bind
              <$> go p rt_exarg rt_allarg'
              <*> go p rt_ty rt_ty'

    go _ (Liquid.RExprArg e) (Liquid.RExprArg e')
      | e == e' = pure $ Liquid.RExprArg e

    go p Liquid.RAppTy {..}
         Liquid.RAppTy {rt_arg = rt_arg', rt_res = rt_res', rt_reft = rt_reft'}
      = makeAppTy <$> go p rt_arg rt_arg' <*> go p rt_res rt_res'
      where
        makeAppTy arg res
          = Liquid.RAppTy
              { rt_arg  = arg
              , rt_res  = res
              , rt_reft = Liquid.meetOrJoin p rt_reft rt_reft'
              }

    go p (Liquid.RHole r) (Liquid.RHole r') = pure $ Liquid.RHole $ Liquid.meetOrJoin p r r'

    go _ τ τ'
      = Error.throwError Liquid.ErrDoesNotUnify
          { pos       = errPos
          , msg       = Pretty.text errMsg
          , leftType  = Pretty.pprint τ
          , rightType = Pretty.pprint τ'
          }

    go'
      :: Joinable r'
      => Polarity
      -> RSort
      -> RSort
      -> StateT (UnificationState r') m RSort
    go' p τ τ' = void <$> go p (τ $> mempty) (τ' $> mempty)

    goTVInfo
      :: Joinable r'
      => RTVInfo RSort
      -> RTVInfo RSort
      -> StateT (UnificationState r') m (RTVInfo RSort)
    goTVInfo (Liquid.RTVNoInfo _) i = pure i
    goTVInfo i (Liquid.RTVNoInfo _) = pure i
    goTVInfo i@Liquid.RTVInfo {..} Liquid.RTVInfo {rtv_kind = rtv_kind'}
      = makeInfo <$> go' Liquid.Positive rtv_kind rtv_kind'
      where makeInfo kind = i { Liquid.rtv_kind = kind }

    goPVars
      :: Joinable r'
      => PVar RSort
      -> PVar RSort
      -> StateT (UnificationState r') m (PVar RSort)
    goPVars t@Liquid.PV {..}
            u@Liquid.PV {pname = pname', ptype = ptype', parg = parg', pargs = pargs'}
      | pname == pname' && parg == parg'
          = makePVar <$> go' Liquid.Positive ptype ptype' <*> zipWithM goPVarArg pargs pargs'
      | otherwise
          = Error.throwError Liquid.ErrDoesNotUnify
              { pos       = errPos
              , msg       = Pretty.text errMsg
              , leftType  = Pretty.pprint t
              , rightType = Pretty.pprint u
              }
      where makePVar ty args = t { Liquid.ptype = ty, Liquid.pargs = args }

    goPVarArg
      :: Joinable r'
      => (RSort, Symbol, Expr)
      -> (RSort, Symbol, Expr)
      -> StateT (UnificationState r') m (RSort, Symbol, Expr)
    goPVarArg (τ, s, e) (τ', s', e')
      | e == se = (, s, e) <$> go' Liquid.Positive τ τ'
      | otherwise
          = Error.throwError Liquid.ErrDoesNotUnify
              { pos       = errPos
              , msg       = Pretty.text errMsg
              , leftType  = Pretty.pprint e
              , rightType = Pretty.pprint e'
              }
      where se = Fixpoint.subst1 e' (s', Fixpoint.EVar s)

    goPArgs
      :: Joinable r'
      => RTProp RTyCon RTyVar r'
      -> RTProp RTyCon RTyVar r'
      -> StateT (UnificationState r') m (RTProp RTyCon RTyVar r')
    goPArgs Liquid.RProp {..}
            Liquid.RProp {rf_args = rf_args', rf_body = rf_body'}
      = let las   = HashMap.fromList rf_args
            rargs = HashMap.toList <$> foldrM (uncurry $ insertWithA $ go' Liquid.Positive) las rf_args'
         in Liquid.RProp <$> rargs <*> go Liquid.Positive rf_body rf_body'

    goQVBinds
      :: Joinable r'
      => RType RTyCon RTyVar r'
      -> RType RTyCon RTyVar r'
      -> SpecQVar
      -> SpecQVar
      -> StateT (UnificationState r') m SpecQVar
    goQVBinds τ τ'
      Liquid.QVar {..}
      Liquid.QVar {qv_quotient = quotient', qv_quotients = quotients', qv_type = type'}
      | length qv_quotients == length quotients'
          = Liquid.QVar qv_quotient qv_quotients qv_kind
              <$> go' Liquid.Positive qv_type
                    ( Quotient.renameQVs
                        ( HashMap.fromList
                            $ (quotient', qv_quotient) : zip quotients' qv_quotients
                        ) type'
                    )
      | otherwise
          = Error.throwError Liquid.ErrDoesNotUnify
              { pos       = errPos
              , msg       = Pretty.text errMsg
              , leftType  = Pretty.pprint τ
              , rightType = Pretty.pprint τ'
              }

    goQuotient
      :: Joinable r'
      => Polarity
      -> RType RTyCon RTyVar r'
      -> Symbol
      -> r'
      -> RType RTyCon RTyVar r'
      -> StateT (UnificationState r') m (RType RTyCon RTyVar r')
    goQuotient p uτ q r τ = do
      σ  <- State.get
      σ' <-
        Substitution.addQuotVarSubst
          Substitution.QuotVarInsert
            { unifyMaybeI = doUnifyMaybe
            , unifyBaseI  = x
            , quotientVar = q :=> case τ of
                Liquid.RApp {rt_tycon}
                  | Liquid.QuotientTyCon qtc <- Liquid.rtc_tc rt_tycon ->
                      Substitution.ConcreteQuotient qtc
                _ -> Substitution.EmptyQuotient
            , errorPosI   = errPos
            } σ
      State.put σ' *> makeRQuotient <$> go p uτ τ
      where
        makeRQuotient rt_ty
          = Liquid.RQuotient
              { rt_ty
              , rt_quotient = q
              , rt_reft     = r
              }

    doUnifyMaybe
      :: Joinable r' => UnifyMaybe Symbol RTyCon RTyVar r' (StateT (UnificationState r') m)
    doUnifyMaybe = x -- Liquid.antiUnifyRepWithM (const $ unifyMonotypesMaybe γ)

    applySubstitution
      :: Joinable r'
      => Polarity
      -> RTyVar
      -> r'
      -> RType RTyCon RTyVar r'
      -> StateT (UnificationState r') m (RType RTyCon RTyVar r')
    applySubstitution p variable variableReft baseType
      = addSubstitution variable Substitution.SubstInsert
          { baseType
          , alterType    = \t -> do
              v <- State.lift $ go p baseType t
              σ <- State.lift $ State.gets substitution
              State.put σ $> v
          , insertErrPos = errPos
          , insertErrMsg = errMsg
          , strengthen   = Liquid.meet
          }

rename
  :: Hashable tv
  => HashMap tv tv
  -> HashMap Symbol Symbol
  -> RTypeV v c tv r
  -> RTypeV v c tv r
rename σTV _ τ@Liquid.RVar {rt_var}
  | Just α <- HashMap.lookup rt_var σTV = τ { Liquid.rt_var = α }
  | otherwise                           = τ
rename σTV σQV τ@Liquid.RFun {rt_in, rt_out}
  = τ { Liquid.rt_in  = rename σTV σQV rt_in
      , Liquid.rt_out = rename σTV σQV rt_out
      }
rename σTV σQV τ@Liquid.RAllT {rt_tvbind, rt_ty}
  = τ { Liquid.rt_ty = rename (HashMap.delete (Liquid.ty_var_value rt_tvbind) σTV) σQV rt_ty }
rename σTV σQV τ@Liquid.RAllP {rt_pvbind, rt_ty}
  = τ { Liquid.rt_pvbind = rename σTV σQV <$> rt_pvbind
      , Liquid.rt_ty     = rename σTV σQV rt_ty
      }
rename σTV σQV τ@Liquid.RChooseQ {rt_qvbind = qvbind@Liquid.QVar {..}, rt_ty}
  = τ { Liquid.rt_qvbind = rename σTV σQV <$> qvbind
      , Liquid.rt_ty     = rename σTV (deleteAll (HashMap.delete qv_quotient σQV) qv_quotients) rt_ty
      }
rename σTV σQV τ@Liquid.RQuotient {rt_ty, rt_quotient}
  | Just q <- HashMap.lookup rt_quotient σQV
      = τ { Liquid.rt_quotient = q
          , Liquid.rt_ty       = rename σTV σQV rt_ty
          }
  | otherwise = τ { Liquid.rt_ty = rename σTV σQV rt_ty }
rename σTV σQV τ@Liquid.RApp {rt_args, rt_pargs}
  = τ { Liquid.rt_args  = rename σTV σQV <$> rt_args
      , Liquid.rt_pargs = fmap (rename σTV σQV) <$> rt_pargs
      }
rename σTV σQV τ@Liquid.RAllE {rt_allarg, rt_ty}
  = τ { Liquid.rt_allarg = rename σTV σQV rt_allarg
      , Liquid.rt_ty     = rename σTV σQV rt_ty
      }
rename σTV σQV τ@Liquid.REx {rt_exarg, rt_ty}
  = τ { Liquid.rt_exarg = rename σTV σQV rt_exarg
      , Liquid.rt_ty    = rename σTV σQV rt_ty
      }
rename _ _ τ@Liquid.RExprArg {} = τ
rename σTV σQV τ@Liquid.RAppTy {rt_arg, rt_res}
  = τ { Liquid.rt_arg = rename σTV σQV rt_arg
      , Liquid.rt_res = rename σTV σQV rt_res
      }
rename σTV σQV τ@Liquid.RRTy {rt_env, rt_ty}
  = τ { Liquid.rt_env = fmap (rename σTV σQV) <$> rt_env
      , Liquid.rt_ty  = rename σTV σQV rt_ty
      }
rename _ _ τ@Liquid.RHole {} = τ

renamings
  :: (Foldable t, FromInt tv, Hashable tv)
  => Int
  -> t (RTVar tv (RType c tv ()))
  -> (Int, HashMap tv tv, HashMap tv tv)
renamings fvc = foldl' addRenaming (fvc, HashMap.empty, HashMap.empty)
  where
    addRenaming (!n, !σ, !σ') Liquid.RTVar {ty_var_value}
      = let !tv = Liquid.fromInt n
        in ( n + 1
            , HashMapI.unsafeInsert ty_var_value tv σ
            , HashMapI.unsafeInsert tv ty_var_value σ'
            )

addQuotRenaming
  :: Monoid r
  => (Int, HashMap Symbol Symbol, HashMap Symbol (AUTypeRep Symbol c tv r))
  -> QVU Symbol c tv
  -> (Int, HashMap Symbol Symbol, HashMap Symbol (AUTypeRep Symbol c tv r))
addQuotRenaming (n, σ, σT) Liquid.QVar {..}
  = foldl' addRenaming
      ( n + 1
      , HashMapI.unsafeInsert qv_quotient itv σ
      , HashMapI.unsafeInsert itv qty σT
      ) qv_quotients
    where
      qty = Liquid.toAUTypeRep (qv_type $> mempty)
      itv = Liquid.fromInt n

      addRenaming (!m, !σ', !σT') q
        = let !tv = Liquid.fromInt m
           in (m + 1, HashMapI.unsafeInsert q tv σ', HashMapI.unsafeInsert tv qty σT')

quotientRenamings
  :: (Foldable t, Monoid r)
  => Int
  -> t (QVU Symbol c tv)
  -> (Int, HashMap Symbol Symbol, HashMap Symbol (AUTypeRep Symbol c tv r))
quotientRenamings n = foldl' addQuotRenaming (n, HashMap.empty, HashMap.empty)

isTVInSet :: Hashable tv => HashSet tv -> RTVar tv (RType c tv ()) -> Bool
isTVInSet tvs = (`HashSet.member` tvs) . Liquid.ty_var_value

filterQVs :: HashSet Symbol -> (QVU Symbol c tv, r) -> Maybe (QVU Symbol c tv, r)
filterQVs qvs (qv@Liquid.QVar {..}, r)
  | HashSet.member qv_quotient qvs
      = Just (qv { Liquid.qv_quotients = filter (`HashSet.member` qvs) qv_quotients }, r)
  | q : qs <- filter (`HashSet.member` qvs) qv_quotients
      = Just (qv { Liquid.qv_quotient = q, Liquid.qv_quotients = qs}, r)
  | otherwise = Nothing

unifyRepWithType
  :: Unifiable r t m
  => SrcSpan
  -> String
  -> UnifyTypeRep r
  -> RType c RTyVar r
  -> m (UnifyTypeRep r)
unifyRepWithType errPos errMsg UnifyTypeRep {..} τ = do
  (uτ', σ) <-
    State.runStateT (unifyMonotypes γ repBase $ rename σTV σQV uτ) ust
  Substitution.SubstResult {..} <-
    Substitution.substitute errPos errMsg HashSet.empty substitution uτ'
  pure UnifyTypeRep
    { repBase      = resultType
    , repTypeVars  = filter (isTVInSet freeVars . fst) (repTypeVars ++ tvs)
    , repPredVars  = repPredVars ++ pvs
    , repQuotVars  = Maybe.mapMaybe (filterQVs freeQuotVars) (repQuotVars ++ qvs)
    , repUnifiable = HashMap.filterWithKey (\k _ -> HashSet.member k freeVars) unifiable
    , repQuotTypes = HashMap.filterWithKey (\k _ -> HashSet.member k freeQuotVars) quotientVars
    , repFVCount   = repFVCount'
    , repQVCount   = repQVCount'
    }
  where
    (tvs, pvs, qvs, uτ)     = Liquid.bkUniv τ
    (repFVCount', σTV, σUn) = renamings repFVCount $ map fst tvs
    (repQVCount', σQV, σQT) = quotientRenamings repQVCount $ map fst qvs
    unifiable               = HashMap.union repUnifiable σUn
    qvars                   = HashMap.union repQuotTypes σQT

    γ = UnificationEnv
          { unifiableVars = unifiable
          , unPolarity    = Liquid.Positive
          , ..
          }

    ust
      = Substitution
          { substitutionTV = x
          , substitutionQV = qvars
          }

unifyInSession
  :: Unifiable r t m
  => SrcSpan
  -> String
  -> UnifySession c RTyVar r
  -> RType c RTyVar r
  -> RType c RTyVar r
  -> m (UnifyResult c RTyVar r)
unifyInSession errPos errMsg s@UnifySession {..} τ τ'
  = makeResult <$> State.runStateT (unifyMonotypes γ τ τ') ust
  where
    makeResult (unSkeleton, σ)
      = UnifyResult
          { unSession  = s { unSubstitution = substitutionTV substitution }
          , ..
          }

    γ = UnificationEnv
          { unifiableVars = unUnifiable
          , unPolarity    = Liquid.Positive
          , ..
          }

    ust
      = Substitution
          { substitutionTV = unSubstitution
          , substitutionQV = mempty
          }

applyUnifySession
  :: Unifiable r t m
  => SrcSpan
  -> String
  -> UnifySession c RTyVar r
  -> RType c RTyVar r
  -> StateT (HashSet RTyVar) m (RType c RTyVar r)
applyUnifySession errPos errMsg UnifySession {..} τ = do
  ifreeVars <- State.get
  Substitution.SubstResult {freeVars, resultType} <-
    Substitution.substitute errPos errMsg ifreeVars
      Substitution
        { substitutionTV = unSubstitution
        , substitutionQV = mempty
        } τ
  State.put freeVars $> resultType

addTypeVarToSession :: Hashable tv => tv -> UnifySession c tv r -> UnifySession c tv r
addTypeVarToSession tv us@UnifySession { unUnifiable }
  = us { unUnifiable = HashMap.insert tv tv unUnifiable }

unifyTypeRepVar :: tv -> r -> UnifyTypeRep r
unifyTypeRepVar rt_var rt_reft
  = UnifyTypeRep
      { repQuotTypes = HashMap.empty
      , repUnifiable = HashMap.empty
      , repFVCount   = 0
      , repQVCount   = 0
      , repBase      = Liquid.RVar {..}
      , repTypeVars  = []
      , repPredVars  = []
      , repQuotVars  = []
      }

toUnifyTypeRep :: (Hashable tv, Monoid r) => RType c tv r -> UnifyTypeRep r
toUnifyTypeRep τ
  = UnifyTypeRep
      { repQuotTypes = foldl' addQuotTypes HashMap.empty repQuotVars
      , repUnifiable = foldl' addTyVar HashMap.empty repTypeVars
      , repFVCount   = 0
      , repQVCount   = 0
      , ..
      }
  where
    (repTypeVars, repPredVars, repQuotVars, repBase) = Liquid.bkUniv τ

    addTyVar m (Liquid.RTVar {ty_var_value}, _)
      = HashMapI.unsafeInsert ty_var_value ty_var_value m

    addQuotTypes m (Liquid.QVar {..}, _)
      = let qty        = Liquid.toAUTypeRep (qv_type $> mempty)
            ins v m' k = HashMapI.unsafeInsert k v m'
         in foldl' (ins qty) (HashMapI.unsafeInsert qv_quotient qty m) qv_quotients

fromUnifyTypeRep :: UnifyTypeRep r -> RType c tv r
fromUnifyTypeRep UnifyTypeRep {..} = Liquid.mkUnivs repTypeVars repPredVars repQuotVars repBase
