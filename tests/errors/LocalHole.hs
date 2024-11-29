{-@ LIQUID "--expect-error-containing=Unknown logic name `nowhere`" @-}
{-@ LIQUID "--no-termination" @-}

module LocalHole where

mysum xs = go 0 0
  where
    n = length xs
    {-@ go :: i:{Nat | i <= nowhere} -> _ -> _ @-}
    go i acc
      | i >= n    = acc
      | otherwise = go (i+1) (acc + xs !! i)
