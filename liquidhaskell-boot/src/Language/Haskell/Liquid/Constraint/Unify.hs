{-# LANGUAGE FlexibleContexts          #-}

module Language.Haskell.Liquid.Constraint.Unify (simpleUnify, simpleUnifyWith) where

import           Data.Functor        (void)
import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as M
import           Data.HashSet        (HashSet)
import qualified Data.HashSet        as S
import qualified Data.Maybe          as MB

import           Language.Haskell.Liquid.Types
  ( RRProp
  , RRType
  , RType (..)
  , RSort
  , RTyVar
  , SubsTy
  )
import qualified Language.Haskell.Liquid.Types          as LH

import           Language.Fixpoint.Types
  ( Reftable
  , Subable
  )
import qualified Language.Fixpoint.Types as F

simpleUnify
  :: (Reftable r, Subable r, SubsTy RTyVar RSort r)
  => HashSet RTyVar
  -> RRType r
  -> RRType r
  -> Maybe (HashMap RTyVar (RRType r))
simpleUnify fvs t u = simpleUnifyWith fvs t u mempty

simpleUnifyWith
  :: (Reftable r, Subable r, SubsTy RTyVar RSort r)
  => HashSet RTyVar
  -> RRType r
  -> RRType r
  -> HashMap RTyVar (RRType r)
  -> Maybe (HashMap RTyVar (RRType r))
simpleUnifyWith fvs (RVar v _) u m
  | S.member v fvs = do
      let (f, m') = M.alterF (simpleUnifyUpdate (simpleUnifyWith fvs) u) v m
      f m'
simpleUnifyWith fvs t (RVar v _) m
  | S.member v fvs = do
      let (f, m') = M.alterF (simpleUnifyUpdate (simpleUnifyWith fvs) t) v m
      f m'
simpleUnifyWith _ (RVar lv _) (RVar rv _) m
  | lv == rv = Just m
simpleUnifyWith fvs (RFun _ _ li lo _) (RFun _ _ ri ro _) m = do
  m1 <- simpleUnifyWith fvs li ri m
  simpleUnifyWith fvs lo ro m1
simpleUnifyWith fvs (RAllT lb lt _) (RAllT rb rt _) m = do
  let ltv = LH.ty_var_value lb
      rtv = LH.ty_var_value rb
      lt' = LH.subsTyVarMeet' (ltv, RVar rtv mempty) lt
  simpleUnifyWith (S.delete rtv fvs) lt' rt m
simpleUnifyWith fvs (RAllP lp lt) (RAllP rp rt) m
  | lp == rp = simpleUnifyWith fvs lt rt m
simpleUnifyWith fvs (RApp lc lts lps _) (RApp rc rts rps _) m
  | lc == rc = do
      m1 <- bifoldMaybe (simpleUnifyWith fvs) m lts rts
      bifoldMaybe (simpleUnifyRTProp fvs) m1 lps rps
simpleUnifyWith fvs (RAllE ls la lt) (RAllE rs ra rt) m = do
  let la' = substSym (ls, rs) `F.substa` la
      lt' = substSym (ls, rs) `F.substa` lt
  m1 <- simpleUnifyWith fvs la' ra m
  simpleUnifyWith fvs lt' rt m1
simpleUnifyWith fvs (REx ls la lt) (REx rs ra rt) m = do
  let la' = substSym (ls, rs) `F.substa` la
      lt' = substSym (ls, rs) `F.substa` lt
  m1 <- simpleUnifyWith fvs la' ra m
  simpleUnifyWith fvs lt' rt m1
simpleUnifyWith _ (RExprArg le) (RExprArg re) m
  | le == re  = Just m
simpleUnifyWith fvs (RAppTy lg la _) (RAppTy rg ra _) m = do
  m1 <- simpleUnifyWith fvs lg rg m
  simpleUnifyWith fvs la ra m1
simpleUnifyWith fvs (RAppTy g a _) t m
  = simpleUnifyAppTy fvs (getAppTy g [a]) t m
simpleUnifyWith fvs t (RAppTy g a _) m
  = simpleUnifyAppTy fvs (getAppTy g [a]) t m
simpleUnifyWith fvs (RRTy le _ _ lt) (RRTy re _ _ rt) m = do
  gs <- safeZip (\(ls, _) (rs, _) -> (ls, rs)) le re
  let symap   = M.fromList gs
      symup s = MB.fromMaybe s (M.lookup s symap)
  m1 <- bifoldMaybe (\(_, t) (_, u) -> simpleUnifyWith fvs (symup `F.substa` t) u) m le re
  simpleUnifyWith fvs (symup `F.substa` lt) rt m1
simpleUnifyWith _ (RHole _) (RHole _) m = Just m
simpleUnifyWith _ _ _ _ = Nothing

simpleUnifyAppTy
  :: (Reftable r, Subable r, SubsTy RTyVar RSort r)
  => HashSet RTyVar
  -> (RRType r, [RRType r])
  -> RRType r
  -> HashMap RTyVar (RRType r)
  -> Maybe (HashMap RTyVar (RRType r))
simpleUnifyAppTy fvs (RVar v r, as) t m
  | S.member v fvs && F.isTauto r = case t of
      RApp _ ts _ _  -> bifoldM (simpleUnifyWith fvs) m as ts
      RFun _ _ i o _ -> case as of
        [it]     -> simpleUnifyWith fvs i it m
        [it, ot] -> do
          m1 <- simpleUnifyWith fvs i it m
          simpleUnifyWith fvs o ot m1
        _        -> Nothing
      _                           -> Nothing
  | otherwise                     = Nothing
simpleUnifyAppTy _ _ _ _ = Nothing

simpleUnifyRTProp
  :: (Reftable r, Subable r, SubsTy RTyVar RSort r)
  => HashSet RTyVar
  -> RRProp r
  -> RRProp r
  -> HashMap RTyVar (RRType r)
  -> Maybe (HashMap RTyVar (RRType r))
simpleUnifyRTProp fvs lp rp m = do
  let unifyArgs (ls, lt) (rs, rt) = simpleUnifyWith fvs (substSym (ls, rs) `F.substa` lt) rt
  bifoldMaybe unifyArgs (void <$> m) (LH.rf_args lp) (LH.rf_args rp)
  simpleUnifyWith fvs (LH.rf_body lp) (LH.rf_body rp) m

simpleUnifyUpdate
  :: (a -> b -> c -> Maybe c)
  -> a
  -> Maybe b
  -> (c -> Maybe c, Maybe a)
simpleUnifyUpdate _ t Nothing  = (Just, Just t)
simpleUnifyUpdate f t (Just u) = (f t u, Just t)

getAppTy :: RRType r -> [RRType r] -> (RRType r, [RRType r])
getAppTy (RAppTy f a _) as = getAppTy f (a : as)
getAppTy f as              = (f, as)

substSym :: (F.Symbol, F.Symbol) -> F.Symbol -> F.Symbol
substSym (i, o) s
  | s == i    = o
  | otherwise = s

bifoldM :: Monad m => (a -> b -> c -> m c) -> c -> [a] -> [b] -> m c
bifoldM _ c []       _        = return c
bifoldM _ c _        []       = return c
bifoldM f c (a : as) (b : bs) = do
  nc <- f a b c
  bifoldM f nc as bs

bifoldMaybe :: (a -> b -> c -> Maybe c) -> c -> [a] -> [b] -> Maybe c
bifoldMaybe _ c []       []       = Just c
bifoldMaybe f c (a : as) (b : bs) = do
  nc <- f a b c
  bifoldMaybe f nc as bs
bifoldMaybe _ _ _        _        = Nothing

safeZip :: (a -> b -> c) -> [a] -> [b] -> Maybe [c]
safeZip _ []       []       = Just []
safeZip f (a : as) (b : bs) = (f a b :) <$> safeZip f as bs
safeZip _ _        _        = Nothing
