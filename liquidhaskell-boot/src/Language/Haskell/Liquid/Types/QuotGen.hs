{-# LANGUAGE NamedFieldPuns #-}

module Language.Haskell.Liquid.Types.QuotGen
  ( freeQuotientVars
  , generalizeQV
  ) where

import           Data.Functor                            (void)
import           Data.Hashable                           (Hashable)
import           Data.HashMap.Strict                     (HashMap)
import qualified Data.HashMap.Strict                     as HashMap
import           Data.HashSet                            (HashSet)
import qualified Data.HashSet                            as HashSet

import           Language.Fixpoint.Types                 (Symbol)

import           Language.Haskell.Liquid.Types.AntiUnify (AUTypeRep, FromInt)
import qualified Language.Haskell.Liquid.Types.AntiUnify as Liquid
import           Language.Haskell.Liquid.Types.RType     (RType, RTypeV)
import qualified Language.Haskell.Liquid.Types.RType     as Liquid

unifyFreeQVars
  :: (Eq c, Eq v, FromInt tv, Hashable tv)
  => HashMap Symbol (AUTypeRep v c tv ())
  -> HashMap Symbol (AUTypeRep v c tv ())
  -> HashMap Symbol (AUTypeRep v c tv ())
unifyFreeQVars = HashMap.unionWith Liquid.antiUnifyRep

freeQuotientVars
  :: (Eq c, Eq v, FromInt tv, Hashable tv)
  => HashSet Symbol
  -> RTypeV v c tv r
  -> HashMap Symbol (AUTypeRep v c tv ())
freeQuotientVars bqvs (Liquid.RAllP _ t)   = freeQuotientVars bqvs t
freeQuotientVars bqvs (Liquid.RAllT _ t _) = freeQuotientVars bqvs t
freeQuotientVars bqvs (Liquid.RChooseQ Liquid.QVar {..} t _)
  = let bqvs' = foldl' (flip HashSet.delete) (HashSet.delete qv_quotient bqvs) qv_quotients
     in freeQuotientVars bqvs qv_type `unifyFreeQVars` freeQuotientVars bqvs' t
freeQuotientVars bqvs (Liquid.RQuotient t q _)
  | HashSet.member q bqvs = freeQuotientVars bqvs t
  | otherwise
      = HashMap.insertWith Liquid.antiUnifyRep q (Liquid.AUTypeRep [] $ void t)
          $ freeQuotientVars bqvs t
freeQuotientVars bqvs (Liquid.RFun _ _ t t' _)
  = freeQuotientVars bqvs t `unifyFreeQVars` freeQuotientVars bqvs t'
freeQuotientVars bqvs (Liquid.RApp _ ts _ _)
  = foldl' unifyFreeQVars HashMap.empty $ map (freeQuotientVars bqvs) ts
freeQuotientVars _ (Liquid.RVar _ _) = HashMap.empty
freeQuotientVars bqvs (Liquid.RAllE _ tx t)
  = freeQuotientVars bqvs tx `unifyFreeQVars` freeQuotientVars bqvs t
freeQuotientVars bqvs (Liquid.REx _ tx t)
  = freeQuotientVars bqvs tx `unifyFreeQVars` freeQuotientVars bqvs t
freeQuotientVars _ (Liquid.RExprArg _) = HashMap.empty
freeQuotientVars bqvs (Liquid.RAppTy t t' _)
  = freeQuotientVars bqvs t `unifyFreeQVars` freeQuotientVars bqvs t'
freeQuotientVars _ (Liquid.RHole _) = HashMap.empty
freeQuotientVars bqvs (Liquid.RRTy e _ _ t)
  = foldl' unifyFreeQVars HashMap.empty $ map (freeQuotientVars bqvs) (t:(snd <$> e))

chooseQ :: Monoid r => RTypeV v c tv r -> Symbol -> AUTypeRep v c tv () -> RTypeV v c tv r
chooseQ rt_ty qv_quotient qvt
  = Liquid.RChooseQ
      { rt_qvbind
          = Liquid.QVar
              { qv_quotients = []
              , qv_type      = Liquid.fromAUTypeRep qvt
              , qv_kind      = Liquid.ChooseQ
              , ..
              }
      , rt_ty
      , rt_reft = mempty
      }

generalizeQV :: (Eq c, FromInt tv, Hashable tv, Monoid r) => RType c tv r -> RType c tv r
generalizeQV t = HashMap.foldlWithKey' chooseQ t $ freeQuotientVars HashSet.empty t
