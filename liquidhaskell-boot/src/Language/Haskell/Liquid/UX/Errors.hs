{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE BangPatterns      #-}

-- | This module contains the functions related to @Error@ type,
-- in particular, to @tidyError@ using a solution, and @pprint@ errors.

module Language.Haskell.Liquid.UX.Errors ( tidyError ) where

import           Control.Arrow                       (second)
import           Data.Either                         (partitionEithers)
import qualified Data.HashMap.Strict                 as M
import qualified Data.HashSet                        as S
import qualified Data.List                           as L
import           Data.Hashable
import           Data.Maybe                          (maybeToList)
import qualified Language.Fixpoint.Types             as F
import qualified Language.Fixpoint.Solver.EnvironmentReduction as F
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Transforms.Simplify
import           Language.Haskell.Liquid.UX.Config
import           Language.Haskell.Liquid.UX.Tidy
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RTypeOp
import           Language.Haskell.Liquid.Types.Types
import qualified Language.Haskell.Liquid.GHC.Misc    as GM
import qualified Language.Haskell.Liquid.Misc        as Misc

-- import Debug.Trace

type Ctx  = M.HashMap F.Symbol SpecType
type CtxM = M.HashMap F.Symbol (WithModel SpecType)

------------------------------------------------------------------------
tidyError :: Config -> F.FixSolution -> Error -> Error
------------------------------------------------------------------------
tidyError cfg sol
  = fmap (tidySpecType tidy)
  . tidyErrContext tidy sol
  where
    tidy = configTidy cfg

configTidy :: Config -> F.Tidy
configTidy cfg
  | shortNames cfg = F.Lossy
  | otherwise      = F.Full

tidyErrContext :: F.Tidy -> F.FixSolution -> Error -> Error
tidyErrContext k _ e@(ErrSubType {})
  = e { ctx = c', tact = F.subst θ tA, texp = F.subst θ tE }
    where
      (θ, c') = tidyCtx k xs (ctx e)
      xs      = F.syms tA ++ F.syms tE
      tA      = tact e
      tE      = texp e

tidyErrContext _ _ e@(ErrSubTypeModel {})
  = e { ctxM = c', tactM = fmap (F.subst θ) tA, texp = fmap (F.subst θ) tE }
    where
      (θ, c') = tidyCtxM xs $ ctxM e
      xs      = F.syms tA ++ F.syms tE
      tA      = tactM e
      tE      = texp e

tidyErrContext k _ e@(ErrAssType {})
  = e { ctx = c', cond = F.subst θ p }
    where
      m       = ctx e
      (θ, c') = tidyCtx k xs m
      xs      = F.syms p
      p       = cond e

tidyErrContext _ _ e
  = e

--------------------------------------------------------------------------------
tidyCtx       :: F.Tidy -> [F.Symbol] -> Ctx -> (F.Subst, Ctx)
--------------------------------------------------------------------------------
tidyCtx k xs m = (θ1 `mappend` θ2, M.fromList yts)
  where
    yts        = [tBind x (tidySpecType k t) | (x, t) <- xt2s]
    (θ2, xt2s) = tidyREnv xt1s
    (θ1, xt1s) = tidyTemps xts
    xts        = sliceREnv xs m
    tBind x t  = (x', shiftVV t x') where x' = F.tidySymbol x

tidyCtxM       :: [F.Symbol] -> CtxM -> (F.Subst, CtxM)
tidyCtxM xs m  = (θ, M.fromList yts)
  where
    yts       = [tBind x t | (x, t) <- xts]
    (θ, xts)  = tidyTemps $ second (fmap stripReft) <$> tidyREnvM xs m
    tBind x t = (x', fmap (`shiftVV` x') t) where x' = F.tidySymbol x

tidyREnv :: [(F.Symbol, SpecType)] -> (F.Subst, [(F.Symbol, SpecType)])
tidyREnv xts    = (θ, second (F.subst θ) <$> zts)
  where
    θ           = expandVarDefs yes
    (yes, zts)  = partitionEithers $ map isInline xts

-- | 'expandVarDefs [(x1, e1), ... ,(xn, en)] returns a `Subst` that  
--   contains the fully substituted definitions for each `xi`. For example, 
--      expandVarDefs [(x1, 'x2 + x3'), (x5, 'x1 + 1')] 
--   should return 
--     [x1 := 'x2 + x3, x5 := (x2 + x3) + 1]

expandVarDefs :: [(F.Symbol, F.Expr)] -> F.Subst
expandVarDefs      = go mempty
  where
    go !su xes
      | null yes   = su `mappend` F.mkSubst xes
      | otherwise  = go (su `mappend` su') xes''
      where
       xes''       = [(z, F.subst su' e) | (z, e) <- zes]
       xs          = S.fromList [x | (x, _) <- xes]
       su'         = F.mkSubst yes
       (yes, zes)  = L.partition (isDef xs . snd) xes
    isDef xs e     = not (any (`S.member` xs) (F.syms e))

isInline :: (a, SpecType) -> Either (a, F.Expr) (a, SpecType)
isInline (x, t) =
    either (Left . (x,)) (Right . (x,)) (isInline' t')
  where
    -- tidyInternalRefas could drop some conjuncts which affects whether
    -- bindings are eliminated in isInline'
    t' = tidyInternalRefas t

isInline' :: SpecType -> Either F.Expr SpecType
isInline' t = case ro of
                Nothing -> Right t'
                Just rr -> case F.isSingletonReft (ur_reft rr) of
                  Just e -- Treat as singleton only if there aren't other conjucts
                    | [_] <- F.conjuncts (F.reftPred (ur_reft rr)) -> Left e
                  _ -> Right (strengthen t' rr)
              where
                  (t', ro) = stripRType t

stripReft     :: SpecType -> SpecType
stripReft t   = maybe t' (strengthen t') ro
  where
    (t', ro)  = stripRType t

stripRType    :: SpecType -> (SpecType, Maybe RReft)
stripRType st = (t', ro)
  where
    t'        = fmap (const (uTop mempty)) t
    ro        = stripRTypeBase  t
    t         = simplifyBounds st

-- | @sliceREnv xs m@ collects all bindings needed by @xs@.
-- A symbol needs a binding, if the binding binds the symbol, or it contains the
-- symbol, or it contains symbols used by bindings that are needed by the
-- symbol.
sliceREnv :: [F.Symbol] -> Ctx -> [(F.Symbol, SpecType)]
sliceREnv xs m =
    [(x, t) | x <- relatedSyms, Just t <- [M.lookup x m], ok t]
  where
    directlyUses = M.map (F.exprSymbolsSet . F.reftPred . rTypeReft) m
    relatedSyms = L.sort $ S.toList $ F.relatedSymbols (S.fromList xs) directlyUses
    ok        = not . isFunTy

tidyREnvM      :: [F.Symbol] -> CtxM -> [(F.Symbol, WithModel SpecType)]
tidyREnvM xs m = [(x, t) | x <- xs', t <- maybeToList (M.lookup x m), ok t]
  where
    xs'       = expandFix deps xs
    deps y    = maybe [] (F.syms . rTypeReft . dropModel) (M.lookup y m)
    ok        = not . isFunTy . dropModel

expandFix :: (Eq a, Hashable a) => (a -> [a]) -> [a] -> [a]
expandFix f               = S.toList . go S.empty
  where
    go seen []            = seen
    go seen (x:xs)
      | x `S.member` seen = go seen xs
      | otherwise         = go (S.insert x seen) (f x ++ xs)

tidyTemps     :: (F.Subable t) => [(F.Symbol, t)] -> (F.Subst, [(F.Symbol, t)])
tidyTemps xts = (θ, [(txB x, txTy t) | (x, t) <- xts])
  where
    txB  x    = M.lookupDefault x x m
    txTy      = F.subst θ
    m         = M.fromList yzs
    θ         = F.mkSubst [(y, F.EVar z) | (y, z) <- yzs]
    yzs       = zip ys niceTemps
    ys        = [ x | (x,_) <- xts, GM.isTmpSymbol x]

niceTemps     :: [F.Symbol]
niceTemps     = mkSymbol <$> xs ++ ys
  where
    mkSymbol  = F.symbol . ('?' :)
    xs        = Misc.single <$> ['a' .. 'z']
    ys        = ("a" ++) <$> [show n | n <- [(0::Int) ..]]
