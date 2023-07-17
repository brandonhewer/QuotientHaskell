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
example (Bin x t u) = Bin x t u
