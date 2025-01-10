module MyBagDefine where

import MyBag as B
import Data.Set

{- dropping the qualification will trigger the "Ambiguous specification symbol" error -}
{-@ define B.empty = (Bag_empty 0) @-}
{-@ define sng k = (Bag_sng k 1) @-}

{-@ thm_emp :: x:k -> { B.empty /= sng x } @-}
thm_emp :: (Ord k) => k -> ()
thm_emp x = const () (sng x)
