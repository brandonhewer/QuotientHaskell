{-@ LIQUID "--reflection" @-}

module Boom where

data Tree a = Empty | Leaf a | Join (Tree a) (Tree a)
  
{-@
data List a
  =  Tree a
  |/ idl   :: x:List a -> Join Empty x == x
  |/ idr   :: x:List a -> Join x Empty == x
  |/ assoc :: x:List a -> y:List a -> z:List a -> Join (Join x y) z == Join x (Join y z)
@-}

{-@
data Bag a
  =  List a
  |/ comm :: xs:Bag a -> ys:Bag a -> Join xs ys == Join ys xs
@-}

{-@
data Set a
  =  Bag a
  |/ idem :: xs:Set a -> Join xs xs == xs
@-}

{-@ reflect prepend @-}
{-@ prepend :: [a] -> List a -> [a] @-}
prepend :: [a] -> Tree a -> [a]
prepend xs Empty      = xs
prepend xs (Leaf x)   = x : xs
prepend xs (Join t u) = prepend (prepend xs t) u

{-@ reflect toList @-}
{-@ toList :: List a -> [a] @-}
toList :: Tree a -> [a]
toList t = prepend [] t

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

{-@ reflect sumB @-}
{-@ sumB :: Bag Int -> Int @-}
sumB :: Tree Int -> Int
sumB Empty      = 0
sumB (Leaf n)   = n
sumB (Join x y) = sumB x + sumB y

{-@ reflect contains @-}
{-@ contains :: Int -> Set Int -> Bool @-}
contains :: Int -> Tree Int -> Bool
contains _ Empty      = False
contains x (Leaf y)   = x == y
contains x (Join t u) = contains x t || contains x u

{-@ sumL :: List Int -> Int @-}
sumL :: Tree Int -> Int
sumL t = sumB t
