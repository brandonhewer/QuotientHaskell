{-@ LIQUID "--reflection" @-}

module Polar where

{-@ type Magnitude = { r:Double | r >= 0 } @-}

{-@
data Polar
  =  (Magnitude, Int)
  |/ turn :: r:Magnitude -> a:Int -> (r, a) == (r, a + 360)
@-}

{-@ rotate :: Int -> Polar -> Polar @-}
rotate :: Int -> (Double, Int) -> (Double, Int)
rotate x (r, a) = (r, a + x)

data Tree a = Empty | Leaf a | Join (Tree a) (Tree a)

{-@ reflect cons @-}
cons :: a -> [a] -> [a]
cons x xs = x : xs

{-@
data Bag a
  =  [a]
  |/ comm :: x:a -> y:a -> xs:[a] -> x : y : xs == cons y (cons x xs)
@-}
