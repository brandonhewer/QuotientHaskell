module Boom where

data Tree a = Empty | Leaf a | Join (Tree a) (Tree a)
  
{-@
data List a
  =  Tree a
  |/ idl :: x:List a -> Join Empty x == x
  |/ idr :: x:List a -> Join x Empty == x
  |/ assoc :: x:List a -> y:List a -> z:List a -> Join (Join x y) z == Join x (Join y z)
@-}

{-@ reflect lmap @-}
{-@ lmap :: (a -> b) -> List a -> List b @-}
lmap :: (a -> b) -> Tree a -> Tree b
lmap _ Empty      = Empty
lmap f (Leaf a)   = Leaf (f a)
lmap f (Join t u) = Join (lmap f t) (lmap f u)

{-@ reflect lfilter @-}
{-@ lfilter :: (a -> Bool) -> List a -> List a @-}
lfilter :: (a -> Bool) -> Tree a -> Tree a
lfilter _ Empty = Empty
lfilter p (Leaf x)
  | p x       = Leaf x
  | otherwise = Empty
lfilter p (Join x y) = Join (lfilter p x) (lfilter p y)

{-@ reflect notAllow @-}
{-@ notAllow :: List a -> Tree a @-}
notAllow :: Tree a -> Tree a
notAllow Empty = Empty
notAllow (Leaf a) = Leaf a
notAllow (Join x y) = Join x y

{-
{-@ reflect sumT @-}
{-@ sumT :: List Int -> Int @-}
sumT :: Tree Int -> Int
sumT Empty      = 0
sumT (Leaf n)   = n
sumT (Join x y) = sumT x + sumT y-}

{-
{-@ reflect subtr @-}
{-@ subtr :: List Int -> Int @-}
subtr :: Tree Int -> Int
subtr Empty = 0
subtr (Leaf n) = n
subtr (Join x y) = subtr x - subtr y-}
