module MyBag where

import qualified Data.Map as M

{-@ embed Bag as Bag_t @-}
data Bag a = Bag { toMap :: M.Map a Int } deriving Eq

{-@ assume empty :: {v:Bag k | v = Bag_empty 0} @-}
empty :: Bag k
empty = Bag M.empty

{-@ assume sng :: (Ord k) => k:k -> {v:Bag k | v = Bag_sng k 1} @-}
sng :: (Ord k) => k -> Bag k
sng k = Bag (M.singleton k 1)
