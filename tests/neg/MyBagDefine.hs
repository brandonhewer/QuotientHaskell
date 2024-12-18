{-@ LIQUID "--expect-any-error" @-}
module MyBagDefine where

import MyBag
import Data.Set

{-@ define empty = (Bag_empty 0) @-}
{-@ define sng k = (Bag_sng k 1) @-}

{-@ thm_emp :: x:k -> { empty /= sng x } @-}
thm_emp :: (Ord k) => k -> ()
thm_emp x = const () (sng x)
