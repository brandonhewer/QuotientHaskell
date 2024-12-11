module Maps1 where

import Prelude hiding (lookup)
import Data.Map

{-@ prop0   :: _ -> x:_ -> y:{_ | y == x} -> TT @-}
prop0       :: Map Int Int -> Int -> Int -> Bool
prop0 m x y = (a == b)
  where
    a       = m ! x
    b       = m ! y

{-@ prop1   :: _ -> x:_ -> y:{_ | y /= x} -> TT @-}
prop1       :: Map Int Int -> Int -> Int -> Bool
prop1 m x y = (z == 10)
  where
    m1      = insert x 10 m
    m2      = insert y 20 m1
    z       = m2 ! x

{-@ prop2   :: _ -> x:_ -> y:{_ | y == x} -> TT @-}
prop2       :: (Eq v, Num v, Ord k) => Map k v -> k -> k -> Bool
prop2 m x y = (z == 20)
  where
    m1      = insert x 10 m
    m2      = insert y 20 m1
    z       = m2 ! x

-----------------------------------------------------------------------

{-@ embed Map as Map_t @-}
{-@ assume (!)         :: (Ord k) => m:Map k v -> k:k -> {v:v | v = Map_select m k} @-}
{-@ assume insert      :: (Ord k) => key:k -> value:v -> m:Map k v -> {n:Map k v | n = Map_store m key value} @-}

-----------------------------------------------------------------------
