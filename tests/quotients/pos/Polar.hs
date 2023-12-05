{-@ LIQUID "--reflection" @-}

module Polar where

{-@ type Magnitude = { r:Double | r >= 0 } @-}

{-@
data Polar
  =  (Magnitude, Int)
  |/ turn :: r:Magnitude -> a:Int -> (r, a) == (r, a + 360)
@-}

{-@ reflect rotate @-}
{-@ rotate :: Int -> Polar -> Polar @-}
rotate :: Int -> (Double, Int) -> (Double, Int)
rotate x (r, a) = (r, a + x)
