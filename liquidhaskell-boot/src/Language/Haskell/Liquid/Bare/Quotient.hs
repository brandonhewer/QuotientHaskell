{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}

module Language.Haskell.Liquid.Bare.Quotient
  ( quotTCAppWith
  ) where

import           Data.HashSet                           (HashSet)
import qualified Data.HashSet                           as HashSet

import           Language.Fixpoint.Types                (Located, Symbol)
import qualified Language.Fixpoint.Types                as Fixpoint
import qualified Language.Haskell.Liquid.GHC.Misc       as Source
import qualified Language.Haskell.Liquid.Types.Errors   as Error
import           Language.Haskell.Liquid.Types.QuotDecl (QuotDeclR, QuotDeclP (..))
import           Language.Haskell.Liquid.Types.RType
  ( Reftable
  , RRType
  , RTProp
  , RTyCon
  , RType
  , RTypeV (..)
  , RTyVar
  , TyConInfo
  , UTyCon (..)
  )
import qualified Language.Haskell.Liquid.Types.RType    as Liquid
import           Language.Haskell.Liquid.Types.Types    (Error)
import           Language.Haskell.Liquid.Types.Variance (Variance (..), VarianceInfo)
import qualified Language.Haskell.Liquid.Types.Variance as Variance

import           Liquid.GHC.API                         (Module)

import qualified Text.PrettyPrint.HughesPJ              as Pretty

adjust :: Eq k => (v -> v) -> k -> [(k, v)] -> [(k, v)]
adjust _ _ [] = []
adjust f k ((ik , iv) : kvs)
  | k == ik   = (ik, f iv) : kvs
  | otherwise = (ik, iv) : adjust f k kvs

uTyConVariance :: UTyCon -> VarianceInfo
uTyConVariance (GHCTyCon c)                      = Variance.makeTyConVariance c
uTyConVariance QuotientTyCon {qtc_tvs, qtc_base} = computeVariances qtc_tvs qtc_base

computeVariances :: [Symbol] -> RRType r -> VarianceInfo
computeVariances tvs = map snd . go HashSet.empty Covariant (map (, Variance.Invariant) tvs)
  where
    go :: HashSet Symbol -> Variance -> [(Symbol, Variance)] -> RRType r -> [(Symbol, Variance)]
    go bvs variance vs RVar {rt_var}
      | HashSet.member varSym bvs = vs
      | otherwise                 = adjust (<> variance) varSym vs
      where
        varSym :: Symbol
        varSym = Fixpoint.symbol rt_var
    go bvs variance vs RFun {rt_in, rt_out}
      = go bvs variance (go bvs (Variance.flipVariance variance) vs rt_in) rt_out
    go bvs variance vs RAllT {rt_tvbind, rt_ty}
      = let Liquid.RTV s = Liquid.ty_var_value rt_tvbind
         in go (HashSet.insert (Fixpoint.symbol s) bvs) variance vs rt_ty
    go bvs variance vs RAllP {rt_ty}
      = go bvs variance vs rt_ty
    go bvs variance vs RChooseQ {rt_ty}
      = go bvs variance vs rt_ty
    go bvs variance vs RQuotient {rt_ty}
      = go bvs variance vs rt_ty
    go bvs variance vs RApp {rt_tycon = Liquid.RTyCon {rtc_tc}, rt_args}
      = let cvs             = uTyConVariance rtc_tc
            next ivs (v, t) = go bvs (v <> variance) ivs t
         in foldl' next vs $ zip cvs rt_args
    go bvs variance vs RAllE {rt_allarg, rt_ty}
      = go bvs variance (go bvs (Variance.flipVariance variance) vs rt_allarg) rt_ty
    go bvs variance vs REx {rt_exarg, rt_ty}
      = go bvs variance (go bvs (Variance.flipVariance variance) vs rt_exarg) rt_ty
    go _ _ vs RExprArg {} = vs
    go bvs variance vs RAppTy {rt_arg, rt_res}
      = go bvs variance (go bvs variance vs rt_arg) rt_res
    go bvs variance vs RRTy {rt_env, rt_ty}
      = let vs'             = Variance.flipVariance variance
            next ivs (_, t) = go bvs vs' ivs t
         in foldl' next (go bvs variance vs rt_ty) rt_env
    go _ _ vs RHole {} = vs

quotTCAppWith
  :: forall r
   . Reftable r
  => QuotDeclR r
  -> Module
  -> Located Symbol
  -> r
  -> [RTProp RTyCon RTyVar r]
  -> [RType RTyCon RTyVar r]
  -> Either [Error] (RType RTyCon RTyVar r)
quotTCAppWith QuotDecl {..} qtc_module (Fixpoint.Loc l _ s) rt_reft rt_pargs rt_args
  | tyVarCount >= argCount = Right $ qTyApp qtycType
  | otherwise
      = Left
          [ Error.ErrQuotientApp
              (Source.sourcePosSrcSpan l)
              (Fixpoint.pprint s)
              (Source.sourcePosSrcSpan $ Fixpoint.loc qtycName)
              ( Pretty.hcat
                  [ Pretty.text "Expects"
                  , Fixpoint.pprint tyVarCount
                  , Pretty.text "arguments, but is given"
                  , Fixpoint.pprint argCount
                  ]
              )
          ]
  where
    qTyApp :: RRType r -> RRType r
    qTyApp qtc_base
      = Liquid.RApp
          { rt_tycon
              = Liquid.RTyCon
                  Liquid.QuotientTyCon
                    { qtc_name = qtycName
                    , qtc_tvs  = qtycTyVars
                    , qtc_base = Liquid.ofReft . Liquid.toReft <$> qtc_base
                    , ..
                    } [] $ tyConInfo qtc_base
          , ..
          }

    tyConInfo :: RRType r -> TyConInfo
    tyConInfo qtc_base
      = Liquid.TyConInfo
          { varianceTyArgs = computeVariances qtycTyVars qtc_base
          , variancePsArgs = []
          , sizeFunction   = Nothing
          }

    tyVarCount :: Int
    tyVarCount = length qtycTyVars

    argCount :: Int
    argCount = length rt_args
