module Map where

{-@
data Test
  =  Int
  |/ test :: 0 == 3
@-}

{-@ fun :: Test -> Test @-}
fun :: Int -> Int
fun 2 = 3
fun n = n
