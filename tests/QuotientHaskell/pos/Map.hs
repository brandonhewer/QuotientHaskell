module Map where

{-@
data Test
  =  Int
  |/ test :: 0 == 3
@-}

{-@ fun :: choose <q :: Int>. Int -> Int @-}
fun :: Int -> Int
fun 2 = 3
fun n = n
