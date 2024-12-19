{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.Set_LHAssumptions where

import Data.Set
import Data.Set.Internal as I
import GHC.Types_LHAssumptions()
import Prelude hiding (null)

{-@

embed Set as Set_Set

//  ---------------------------------------------------------------------------------------------
//  -- | Refined Types for Data.Set Operations --------------------------------------------------
//  ---------------------------------------------------------------------------------------------

assume isSubsetOf    :: (Ord a) => x:(Set a) -> y:(Set a) -> {v:Bool | v <=> Set_sub x y}
assume member        :: Ord a => x:a -> xs:(Set a) -> {v:Bool | v <=> Set_mem x xs}
assume null          :: Ord a => xs:(Set a) -> {v:Bool | v <=> Set_emp xs}

assume empty         :: {v:(Set a) | Set_emp v}
assume singleton     :: x:a -> {v:(Set a) | v = (Set_sng x)}
assume insert        :: Ord a => x:a -> xs:(Set a) -> {v:(Set a) | v = Set_cup xs (Set_sng x)}
assume delete        :: (Ord a) => x:a -> xs:(Set a) -> {v:(Set a) | v = Set_dif xs (Set_sng x)}

assume union         :: Ord a => xs:(Set a) -> ys:(Set a) -> {v:(Set a) | v = Set_cup xs ys}
assume intersection  :: Ord a => xs:(Set a) -> ys:(Set a) -> {v:(Set a) | v = Set_cap xs ys}
assume difference    :: Ord a => xs:(Set a) -> ys:(Set a) -> {v:(Set a) | v = Set_dif xs ys}

assume fromList :: Ord a => xs:[a] -> {v:Set a | v = listElts xs}
assume toList   :: Ord a => s:Set a -> {xs:[a] | s = listElts xs}

//  ---------------------------------------------------------------------------------------------
//  -- | The set of elements in a list ----------------------------------------------------------
//  ---------------------------------------------------------------------------------------------

measure listElts :: [a] -> Set a
  listElts []     = {v | (Set_emp v)}
  listElts (x:xs) = {v | v = Set_cup (Set_sng x) (listElts xs) }

define singleton x      = (Set_sng x)
define union x y        = (Set_cup x y)
define intersection x y = (Set_cap x y)
define difference x y   = (Set_dif x y)
define empty            = (Set_empty 0)
define null x           = (Set_emp x)
define member x xs      = (Set_mem x xs)
define isSubsetOf x y   = (Set_sub x y)
define fromList xs      = (Data.Set_LHAssumptions.listElts xs)

define I.singleton x      = (Set_sng x)
define I.union x y        = (Set_cup x y)
define I.intersection x y = (Set_cap x y)
define I.difference x y   = (Set_dif x y)
define I.empty            = (Set_empty 0)
define I.null x           = (Set_emp x)
define I.member x xs      = (Set_mem x xs)
define I.isSubsetOf x y   = (Set_sub x y)
define I.fromList xs      = (Data.Set_LHAssumptions.listElts xs)

@-}
