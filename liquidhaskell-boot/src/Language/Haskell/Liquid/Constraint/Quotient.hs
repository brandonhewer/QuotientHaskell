{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor  #-}
{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE NamedFieldPuns #-}

module Language.Haskell.Liquid.Constraint.Quotient
  ( SplitEqConParams (..)
  , splitEqConParams
  ) where

import           Control.Monad.State.Strict                     (StateT)
import qualified Control.Monad.State.Strict                     as State
import qualified Control.Monad.Except                           as Error
import           Data.Foldable                                  (traverse_)
import           Data.Functor                                   (($>))
import           Data.HashMap.Strict                            (HashMap)
import qualified Data.HashMap.Strict                            as HashMap
import qualified Data.HashMap.Internal                          as HashMapI

import           GHC.Types.SrcLoc                               (SrcSpan)

import           Language.Fixpoint.Types
  ( Brel
  , Constant
  , Expr
  , Expression
  , ExprV
  , Reft
  , Sort
  , Symbol
  )
import qualified Language.Fixpoint.Types                        as Fixpoint
import           Language.Haskell.Liquid.Constraint.Env         ((?=), (+=))
import qualified Language.Haskell.Liquid.Constraint.Env         as Environment
import qualified Language.Haskell.Liquid.Constraint.Monad       as Constraint
import           Language.Haskell.Liquid.Constraint.QuotEnv     (EqualityTerm)
import qualified Language.Haskell.Liquid.Constraint.QuotEnv     as Quotient
import           Language.Haskell.Liquid.Constraint.Types       (CG, CGEnv)
import qualified Language.Haskell.Liquid.Constraint.Types       as Constraint
import qualified Language.Haskell.Liquid.Constraint.Unification as Unification
import qualified Language.Haskell.Liquid.GHC.Misc               as GM
import           Language.Haskell.Liquid.Types.QuotDecl         (EqualityParamP)
import qualified Language.Haskell.Liquid.Types.QuotDecl         as Quotient
import qualified Language.Haskell.Liquid.Types.RefType          as Liquid
import           Language.Haskell.Liquid.Types.RType            (RTyCon, RTypeV, SpecType, UReftV)
import qualified Language.Haskell.Liquid.Types.RType            as Liquid
import qualified Language.Haskell.Liquid.Types.RTypeOp          as Liquid
import           Language.Haskell.Liquid.Types.Types            (Error)

import qualified Liquid.GHC.API                                 as GHC

data SplitEqConParams v c tv r
  = SplitEqConParams
      { preconditions :: ![ExprV v]
      , binds         :: !(HashMap Symbol (RTypeV v c tv r))
      }

data EqualityTermWithParams c tv r
  = EqualityTermWithParams
      { eqParameters :: !(SplitEqConParams Symbol c tv r)
      , eqTerm       :: !EqualityTerm
      }

splitEqConParams :: [EqualityParamP v (RTypeV v c tv r)] -> SplitEqConParams v c tv r
splitEqConParams = uncurry SplitEqConParams . go [] HashMap.empty
  where
    go cs xs [] = (cs, xs)
    go cs xs (Quotient.EqualityPrecondition c : ps) = go (c : cs) xs ps
    go cs xs (Quotient.EqualityBindParam {..} : ps)
      = go cs (HashMapI.unsafeInsert epBinder (Fixpoint.val epType) xs) ps

toEqualityTerm :: SplitEqConParams Symbol c tv r -> Expr -> EqualityTermWithParams c tv r
toEqualityTerm ips = f . go ips
  where
    go ps e@(Fixpoint.EVar v)
      | isDataCon v = x
      | otherwise   = Quotient.VariableP v
    go ps e@(Fixpoint.EApp f a) = goApp f [a]

    goApp (Fixpoint.EApp f a) as = goApp f (a : as)
    goApp (Fixpoint.EVar constructor) as
      = Quotient.ApplyP
          { constructor
          , arguments = y
          }

    isDataCon s = case Text.uncons (Text.takeWhileEnd (/= '.') (Fixpoint.symbolText s)) of
      Just (c, _) -> Char.isUpper c || c == ':'
      Nothing -> False
