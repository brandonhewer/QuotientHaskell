{-# LANGUAGE NamedFieldPuns #-}

module Language.Haskell.Liquid.Types.QuotGen
  ( freeQuotientVars
  , generalizeQV
  ) where

import           Data.Functor                            (void)
import           Data.Hashable                           (Hashable)
import           Data.HashMap.Strict                     (HashMap)
import qualified Data.HashMap.Strict                     as HashMap

import           Language.Fixpoint.Types                 (Symbol)

import           Language.Haskell.Liquid.Types.QuotUnify (FromInt)
import qualified Language.Haskell.Liquid.Types.QuotUnify as Quotient
import           Language.Haskell.Liquid.Types.RType     (RType, RTypeV)
import qualified Language.Haskell.Liquid.Types.RType     as Liquid

unifyFreeQVars
  :: (Eq c, FromInt tv, Hashable tv)
  => HashMap Symbol (RTypeV v c tv ())
  -> HashMap Symbol (RTypeV v c tv ())
  -> HashMap Symbol (RTypeV v c tv ())
unifyFreeQVars = HashMap.unionWith Quotient.unifyQVarTypes

freeQuotientVars
  :: (Eq c, FromInt tv, Hashable tv)
  => RTypeV v c tv r
  -> HashMap Symbol (RTypeV v c tv ())
freeQuotientVars (Liquid.RAllP _ t)   = freeQuotientVars t
freeQuotientVars (Liquid.RAllT _ t _) = freeQuotientVars t
freeQuotientVars (Liquid.RChooseQ Liquid.QVar {..} t _)
  = let qvs = freeQuotientVars qv_type `unifyFreeQVars` freeQuotientVars t
     in foldl' (flip HashMap.delete) (HashMap.delete qv_quotient qvs) qv_quotients
freeQuotientVars (Liquid.RQuotient t q _)
  = HashMap.insertWith Quotient.unifyQVarTypes q (void t) $ freeQuotientVars t
freeQuotientVars (Liquid.RFun _ _ t t' _)
  = freeQuotientVars t `unifyFreeQVars` freeQuotientVars t'
freeQuotientVars (Liquid.RApp _ ts _ _)
  = foldl' unifyFreeQVars HashMap.empty $ map freeQuotientVars ts
freeQuotientVars (Liquid.RVar _ _) = HashMap.empty
freeQuotientVars (Liquid.RAllE _ tx t)
  = freeQuotientVars tx `unifyFreeQVars` freeQuotientVars t
freeQuotientVars (Liquid.REx _ tx t)
  = freeQuotientVars tx `unifyFreeQVars` freeQuotientVars t
freeQuotientVars (Liquid.RExprArg _) = HashMap.empty
freeQuotientVars (Liquid.RAppTy t t' _)
  = freeQuotientVars t `unifyFreeQVars` freeQuotientVars t'
freeQuotientVars (Liquid.RHole _) = HashMap.empty
freeQuotientVars (Liquid.RRTy e _ _ t)
  = foldl' unifyFreeQVars HashMap.empty $ map freeQuotientVars (t:(snd <$> e))

chooseQ :: Monoid r => RTypeV v c tv r -> Symbol -> RTypeV v c tv () -> RTypeV v c tv r
chooseQ rt_ty qv_quotient qv_type
  = Liquid.RChooseQ
      { rt_qvbind
          = Liquid.QVar
              { qv_quotients = []
              , ..
              }
      , rt_ty
      , rt_reft = mempty
      }

generalizeQV :: (Eq c, FromInt tv, Hashable tv, Monoid r) => RType c tv r -> RType c tv r
generalizeQV t = HashMap.foldlWithKey' chooseQ t $ freeQuotientVars t
