{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Haskell.Liquid.Constraint.Sort
  ( booleanType
  , constantType
  , doubleType
  , integerType
  , stringType
  , sortToSpecType
  ) where

import           Data.IntMap.Strict                      (IntMap)
import qualified Data.IntMap.Strict                      as IntMap
import qualified Data.Maybe                              as Maybe

import           Language.Fixpoint.Types                 (Constant, FTycon, Sort)
import qualified Language.Fixpoint.Types                 as Fixpoint
import qualified Language.Fixpoint.Types.Visitor         as FixVisit
import qualified Language.Haskell.Liquid.GHC.Misc        as GM
import           Language.Haskell.Liquid.Types.AntiUnify (FromInt (..))
import qualified Language.Haskell.Liquid.Types.RefType   as Liquid
import           Language.Haskell.Liquid.Types.RType     (RTyCon, RTypeV, RTyVar)
import qualified Language.Haskell.Liquid.Types.RType     as Liquid
import qualified Language.Haskell.Liquid.Types.RTypeOp   as Liquid

import qualified Liquid.GHC.API                          as GHC

booleanType :: r -> RTypeV v RTyCon tv r
booleanType rt_reft
  = Liquid.RApp
      { rt_tycon = Liquid.tyConRTyCon GHC.boolTyCon
      , rt_args  = []
      , rt_pargs = []
      , rt_reft
      }

stringType :: Monoid r => r -> RTypeV v RTyCon tv r
stringType rt_reft
  = Liquid.RApp
      { rt_tycon = Liquid.tyConRTyCon GHC.listTyCon
      , rt_args
          = [ Liquid.RApp
                { rt_tycon = Liquid.tyConRTyCon GHC.charTyCon
                , rt_args  = []
                , rt_pargs = []
                , rt_reft  = mempty
                }
            ]
      , rt_pargs = []
      , rt_reft
      }

integerType :: r -> RTypeV v RTyCon tv r
integerType rt_reft
  = Liquid.RApp
      { rt_tycon = Liquid.tyConRTyCon GHC.intTyCon
      , rt_args  = []
      , rt_pargs = []
      , rt_reft
      }

doubleType :: r -> RTypeV v RTyCon tv r
doubleType rt_reft
  = Liquid.RApp
      { rt_tycon = Liquid.tyConRTyCon GHC.doubleTyCon
      , rt_args  = []
      , rt_pargs = []
      , rt_reft
      }

constantType :: Monoid r => r -> Constant -> RTypeV v RTyCon tv r
constantType rt_reft Fixpoint.I {} = integerType rt_reft
constantType rt_reft Fixpoint.R {} = doubleType rt_reft
constantType rt_reft (Fixpoint.L _ s)
  | s == Fixpoint.charSort
      = Liquid.RApp
          { rt_tycon = Liquid.tyConRTyCon GHC.charTyCon
          , rt_args  = []
          , rt_pargs = []
          , rt_reft
          }
  | otherwise = stringType rt_reft

functionType :: RTypeV v RTyCon tv r -> RTypeV v RTyCon tv r -> r -> RTypeV v RTyCon tv r
functionType rt_in rt_out rt_reft
  = Liquid.RFun
      { rt_bind  = "_x"
      , rt_rinfo = Liquid.defRFInfo
      , ..
      }

applyType :: Monoid r => (a -> RTypeV v c tv r) -> RTypeV v c tv r -> [a] -> r -> RTypeV v c tv r
applyType toRType f as = (`Liquid.mapRBase` foldl' makeAppTy f as) . const
  where
    makeAppTy rt_arg rs_res
      = let rt_res = toRType rs_res
         in Liquid.RAppTy {rt_reft = mempty, ..}

tyConAppType :: FTycon -> [RTypeV v RTyCon tv r] -> r -> RTypeV v RTyCon tv r
tyConAppType tc rt_args rt_reft
  = Liquid.RApp
      { rt_pargs = []
      , ..
      }
  where
    tc_name = Fixpoint.val $ Fixpoint.fTyconSymbol tc
    rt_tycon
      = Liquid.RTyCon
          { rtc_tc    = Liquid.GHCTyCon $ GM.stringTyCon 'x' 43 $ Fixpoint.symbolString tc_name
          , rtc_pvars = []
          , rtc_info  = Liquid.defaultTyConInfo
          }

sortToSpecType :: Monoid r => Sort -> r -> RTypeV v RTyCon RTyVar r
sortToSpecType Fixpoint.FInt        = integerType
sortToSpecType Fixpoint.FReal       = doubleType
sortToSpecType Fixpoint.FNum        = integerType -- | Change to numeric class type
sortToSpecType Fixpoint.FFrac       = doubleType  -- | Change to fractional class type
sortToSpecType (Fixpoint.FObj s)    = (Liquid.RTV (GM.symbolTyVar s) `Liquid.RVar`)
sortToSpecType (Fixpoint.FVar n)    = (fromInt n `Liquid.RVar`)
sortToSpecType (Fixpoint.FFunc t u)
  = functionType (sortToSpecType t mempty) (sortToSpecType u mempty)
sortToSpecType (Fixpoint.FAbs n s)
  = Liquid.RAllT
      Liquid.RTVar
        { ty_var_value = fromInt n
        , ty_var_info  = Liquid.RTVNoInfo False
        }
      (sortToSpecType s mempty)
sortToSpecType (Fixpoint.FTC c)     = tyConAppType c []
sortToSpecType (Fixpoint.FApp f a)  = appSortToSpecType f [a]

appSortToSpecType :: Monoid r => Sort -> [Sort] -> r -> RTypeV v RTyCon RTyVar r
appSortToSpecType (Fixpoint.FApp f a) as = appSortToSpecType f (a : as)
appSortToSpecType (Fixpoint.FVar n)   as
  = applyType (`sortToSpecType` mempty)
      Liquid.RVar
        { rt_var  = fromInt n
        , rt_reft = mempty
        } as
appSortToSpecType (Fixpoint.FAbs n s) (a : as) = go (IntMap.singleton n a) s as
  where
    go :: Monoid r => IntMap Sort -> Sort -> [Sort] -> r -> RTypeV v RTyCon RTyVar r
    go σ t []                             = sortToSpecType $ sortSubst σ t
    go σ (Fixpoint.FAbs n' s') (a' : as') = go (IntMap.insert n' a' σ) s' as'
    go σ t as'                            = appSortToSpecType (sortSubst σ t) as'
appSortToSpecType (Fixpoint.FTC c)    as = tyConAppType c $ map (`sortToSpecType` mempty) as
appSortToSpecType t                   as
  = applyType (`sortToSpecType` mempty) (sortToSpecType t mempty) as

sortSubst :: IntMap Sort -> Sort -> Sort
sortSubst σ = FixVisit.mapSort f
  where
    f t@(Fixpoint.FVar !i) = Maybe.fromMaybe t $ IntMap.lookup i σ
    f !t                   = t

