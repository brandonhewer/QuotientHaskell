{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Haskell.Liquid.Types.QuotUnify
  ( FromInt (..)
  , unifyQVarTypes
  ) where

import           Control.Monad                           (zipWithM)
import           Control.Monad.State.Strict              (State)
import qualified Control.Monad.State.Strict              as State

import           Data.Functor                            (($>))
import           Data.Hashable                           (Hashable)
import           Data.HashSet                            (HashSet)
import qualified Data.HashSet                            as HashSet

import qualified Language.Fixpoint.Types.Names           as Fixpoint
import qualified Language.Fixpoint.Types.Spans           as Fixpoint

import qualified Language.Haskell.Liquid.GHC.Misc        as GM
import           Language.Haskell.Liquid.Types.RType
  ( BTyVar (..)
  , RTVar  (..)
  , RTypeV (..)
  , RTyVar (..)
  )
import qualified Language.Haskell.Liquid.Types.RType     as Liquid
import qualified Language.Haskell.Liquid.Types.RTypeOp   as Liquid

class FromInt a where
  fromInt :: Int -> a

instance FromInt RTyVar where
  fromInt = RTV . GM.symbolTyVar . Fixpoint.tempSymbol "x" . toInteger

instance FromInt BTyVar where
  fromInt = BTV . Fixpoint.dummyLoc . Fixpoint.tempSymbol "x" . toInteger

data UnifyState tv
  = UnifyState
      { freshTyVars :: !Int
      , unifiedVars :: !(HashSet tv)
      }

emptyUnifyState :: UnifyState tv
emptyUnifyState
  = UnifyState
      { freshTyVars = 0
      , unifiedVars = HashSet.empty
      }

addUnifiedVar :: (Eq tv, Hashable tv) => tv -> State (UnifyState tv) ()
addUnifiedVar tv
  = State.modify' \st@UnifyState {unifiedVars} ->
      st { unifiedVars = HashSet.insert tv unifiedVars }

freshTyVar :: State (UnifyState tv) Int
freshTyVar
  = State.state \st@UnifyState{freshTyVars} ->
      (freshTyVars + 1, st { freshTyVars = freshTyVars + 1 })

unifyZipQVarTypes
  :: (Eq c, Eq tv, FromInt tv, Hashable tv, Monoid r)
  => [RTypeV v c tv r]
  -> [RTypeV v c tv r]
  -> State (UnifyState tv) [RTypeV v c tv r]
unifyZipQVarTypes ts us = zipWithM unifyQVarArgType ts us

unifyQVarArgType
  :: (Eq c, Eq tv, FromInt tv, Hashable tv, Monoid r)
  => RTypeV v c tv r
  -> RTypeV v c tv r
  -> State (UnifyState tv) (RTypeV v c tv r)
unifyQVarArgType RVar {..} _
  = addUnifiedVar rt_var $> RVar {..}
unifyQVarArgType _ RVar {..}
  = addUnifiedVar rt_var $> RVar {..}
unifyQVarArgType t@RFun {rt_bind, rt_rinfo, rt_reft} t'@RFun {}
  = liftA2 mkRFun
      (unifyQVarArgType (rt_in t) $ rt_in t')
      (unifyQVarArgType (rt_out t) $ rt_out t')
  where
    mkRFun rt_in rt_out = RFun {..}
unifyQVarArgType t@RApp {rt_reft, rt_pargs} t'@RApp {}
  | rt_tycon t == rt_tycon t'
      = mkRApp (rt_tycon t) <$> unifyZipQVarTypes (rt_args t) (rt_args t')
  where
    mkRApp rt_tycon rt_args = RApp {..}
unifyQVarArgType t@RAppTy {rt_reft} t'@RAppTy {}
  = mkRAppTy
      <$> unifyQVarArgType (rt_arg t) (rt_arg t')
      <*> unifyQVarArgType (rt_res t) (rt_res t')
  where
    mkRAppTy rt_arg rt_res = RAppTy {..}
unifyQVarArgType _ _
  = makeRVar <$> freshTyVar
  where
    makeRVar n
      = RVar
          { rt_var  = fromInt n
          , rt_reft = mempty
          }

unifyQVarTypes
  :: (Eq c, FromInt tv, Hashable tv, Monoid r)
  => RTypeV v c tv r
  -> RTypeV v c tv r
  -> RTypeV v c tv r
unifyQVarTypes ts us
  = makeType
      $ State.runState
            ( (,) <$> unifyZipQVarTypes (Liquid.ty_args trep) (Liquid.ty_args urep)
                  <*> unifyQVarArgType (Liquid.ty_res trep) (Liquid.ty_res urep)
            ) emptyUnifyState
  where
    trep = Liquid.toRTypeRep ts
    urep = Liquid.toRTypeRep us

    makeTVN n
      = ( Liquid.RTVar
            { ty_var_value = fromInt n
            , ty_var_info  = Liquid.RTVNoInfo False
            }
        , mempty
        )

    makeType ((ty_args, ty_res), UnifyState {..})
      = let count = length ty_args
         in Liquid.fromRTypeRep Liquid.RTypeRep
              { ty_vars  = map makeTVN [1..freshTyVars] ++ map makeTyVar (HashSet.toList unifiedVars)
              , ty_preds = []
              , ty_info  = replicate count Liquid.defRFInfo
              , ty_refts = replicate count mempty
              , ty_binds = replicate count ""
              , ..
              }   

makeTyVar :: Monoid r => tv -> (RTVar tv (RTypeV v c tv ()), r)
makeTyVar ty_var_value
  = ( Liquid.RTVar
        { ty_var_value
        , ty_var_info = Liquid.RTVNoInfo False
        }
    , mempty
    )
