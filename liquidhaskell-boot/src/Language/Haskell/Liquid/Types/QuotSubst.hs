{-# LANGUAGE NamedFieldPuns #-}

module Language.Haskell.Liquid.Types.QuotSubst
  ( renameQVs
  , unfoldQuotientType
  ) where

import           Data.Functor                           (void)
import           Data.HashMap.Strict                    (HashMap)
import qualified Data.HashMap.Strict                    as HashMap

import           Language.Fixpoint.Types                (Symbol)
import qualified Language.Fixpoint.Types                as Fixpoint
import qualified Language.Haskell.Liquid.GHC.Misc       as GM
import           Language.Haskell.Liquid.Types.RType
  ( LHTyCon (..)
  , QTyCon  (..)
  , QVU
  , RRType
  , RTVar   (..)
  , RTypeV  (..)
  , UReftable
  , UTyCon  (..)
  )
import qualified Language.Haskell.Liquid.Types.RType    as Liquid

substituteTVWith
  :: UReftable r'
  => (RRType r -> RRType r') -> HashMap Symbol (RRType r) -> RRType r' -> RRType r'
substituteTVWith f σ v@RVar {rt_var}
  | Just t <- HashMap.lookup var σ = f t
  | otherwise                      = v
  where
    var :: Symbol
    var = Fixpoint.symbol rt_var
substituteTVWith f σ RFun {..}
  = RFun
      { rt_in   = substituteTVWith f σ rt_in
      , rt_out  = substituteTVWith f σ rt_out
      , ..
      }
substituteTVWith f σ RAllT {rt_tvbind = rt_tvbind@RTVar {ty_var_value}, ..}
  = RAllT
      { rt_tvbind = fmap (substituteTVWith void σ) rt_tvbind
      , rt_ty     = substituteTVWith f (HashMap.delete (Fixpoint.symbol ty_var_value) σ) rt_ty
      , ..
      }
substituteTVWith f σ RAllP {..}
  = RAllP
      { rt_pvbind = fmap (substituteTVWith void σ) rt_pvbind
      , rt_ty     = substituteTVWith f σ rt_ty
      }
substituteTVWith f σ RChooseQ {..}
  = RChooseQ
      { rt_qvbind = fmap (substituteTVWith void σ) rt_qvbind
      , rt_ty     = substituteTVWith f σ rt_ty
      , rt_reft
      }
substituteTVWith f σ RQuotient {..}
  = RQuotient
      { rt_ty  = substituteTVWith f σ rt_ty
      , ..
      }
substituteTVWith f σ RApp {rt_tycon = rt_tycon@RTyCon{rtc_tc}, ..}
  = case rtc_tc of
      QuotientTyCon QTyCon {..} -> unfoldQuotientType qtc_tvs rt_args $ fmap Liquid.ofUReft qtc_base
      _                  ->
        RApp
          { rt_args  = map (substituteTVWith f σ) rt_args
          , rt_pargs = map (fmap $ substituteTVWith f σ) rt_pargs
          , ..
          }
substituteTVWith f σ RAllE {..}
  = RAllE
      { rt_allarg = substituteTVWith f σ rt_allarg
      , rt_ty     = substituteTVWith f σ rt_ty
      , ..
      }
substituteTVWith f σ REx {..}
  = REx
      { rt_exarg = substituteTVWith f σ rt_exarg
      , rt_ty    = substituteTVWith f σ rt_ty
      , ..
      }
substituteTVWith _ _ (RExprArg e) = RExprArg e
substituteTVWith f σ RAppTy {..}
  = RAppTy
      { rt_arg = substituteTVWith f σ rt_arg
      , rt_res = substituteTVWith f σ rt_res
      , ..
      }
substituteTVWith f σ RRTy {..}
  = RRTy
      { rt_env = map (fmap $ substituteTVWith f σ) rt_env
      , rt_ty  = substituteTVWith f σ rt_ty
      , ..
      }
substituteTVWith _ _ (RHole r) = RHole r

substituteTV :: UReftable r => HashMap Symbol (RRType r) -> RRType r -> RRType r
substituteTV = substituteTVWith id

zipWithDefault :: (a -> b) -> [a] -> [b] -> [(a, b)]
zipWithDefault f as       []       = map (\a -> (a, f a)) as
zipWithDefault _ []       _        = []
zipWithDefault f (a : as) (b : bs) = (a,b) : zipWithDefault f as bs 

rTyVar :: Monoid r => Symbol -> RRType r
rTyVar = (`RVar` mempty) . Liquid.RTV . GM.symbolTyVar

unfoldQuotientType :: UReftable r => [Symbol] -> [RRType r] -> RRType r -> RRType r
unfoldQuotientType tvs ts = substituteTV (HashMap.fromList $ zipWithDefault rTyVar tvs ts)

renameQVs :: HashMap Symbol Symbol -> RTypeV v c tv r -> RTypeV v c tv r
renameQVs _ RVar {..} = RVar {..}
renameQVs σ RFun {..}
  = RFun
      { rt_in  = renameQVs σ rt_in
      , rt_out = renameQVs σ rt_out
      , ..
      }
renameQVs σ RAllT {..}
  = RAllT
      { rt_ty = renameQVs σ rt_ty
      , ..
      }
renameQVs σ RAllP {..}
  = RAllP
      { rt_ty = renameQVs σ rt_ty
      , ..
      }
renameQVs σ RChooseQ {..}
  = RChooseQ
      { rt_ty = renameQVs (deleteQVs σ rt_qvbind) rt_ty
      , ..
      }
renameQVs σ RQuotient {..}
  = RQuotient
      { rt_ty       = renameQVs σ rt_ty
      , rt_quotient = HashMap.lookupDefault rt_quotient rt_quotient σ
      , ..
      }
renameQVs σ RApp {..}
  = RApp
      { rt_args = map (renameQVs σ) rt_args
      , ..
      }
renameQVs σ RAllE {..}
  = RAllE
      { rt_ty = renameQVs σ rt_ty
      , ..
      }
renameQVs σ REx {..}
  = REx
      { rt_ty = renameQVs σ rt_ty
      , ..
      }
renameQVs _ (RExprArg e) = RExprArg e
renameQVs σ RAppTy {..}
  = RAppTy
      { rt_arg = renameQVs σ rt_arg
      , rt_res = renameQVs σ rt_res
      , ..
      }
renameQVs σ RRTy {..}
  = RRTy
      { rt_env = map (fmap $ renameQVs σ) rt_env
      , rt_ty  = renameQVs σ rt_ty
      , ..
      }
renameQVs _ (RHole r) = RHole r

deleteQVs :: HashMap Symbol Symbol -> QVU v c tv -> HashMap Symbol Symbol
deleteQVs σ Liquid.QVar {qv_quotient, qv_quotients}
  = foldl' (flip HashMap.delete) (HashMap.delete qv_quotient σ) qv_quotients
