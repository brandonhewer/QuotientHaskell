module NumRefl1 where

{-
The `define` should be propagated from NumRefl, otherwise the test fails
with the same error.
-}
import NumRefl

{-@ reflect toNum1 @-}
toNum1 :: Num p => () -> p
toNum1 _ = -2

