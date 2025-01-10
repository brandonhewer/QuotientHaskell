{-# LANGUAGE GADTs #-}
{-@ LIQUID "--expect-any-error" @-}
module RefCtor where

import Language.Haskell.Liquid.ProofCombinators

{-@ type K X Y = { _:F | X = Y } @-}

data F where
{-@ MkF :: x:Int -> y:Int -> K x y @-}
    MkF :: Int -> Int -> F

{-@ falseProof :: { false } @-}
falseProof = () ? MkF 0 2