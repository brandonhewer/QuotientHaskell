module Mobiles where

data Tree a = Leaf | Bin a (Tree a) (Tree a)

{-@
data Mobile a
  =  Tree a
  |/ swap :: x:a -> t:Mobile a -> u:Mobile a -> Bin x t u == Bin x u t
@-}

{-@ example :: Mobile a -> Mobile a @-}
example :: Tree a -> Tree a
example Leaf        = Leaf
example (Bin x t u) = Bin x u t

{-@ tmap :: (a -> b) -> Mobile a -> Mobile b @-}
tmap :: (a -> b) -> Tree a -> Tree b
tmap _ Leaf        = Leaf
tmap f (Bin x t u) = Bin (f x) (tmap f t) (tmap f u)

{-@ filterT :: (a -> Bool) -> Mobile a -> Mobile a @-}
filterT :: (a -> Bool) -> Tree a -> Tree a
filterT _ Leaf        = Leaf
filterT p (Bin x t u)
  | p x       = Leaf
  | otherwise = Bin x (filterT p t) (filterT p u)
