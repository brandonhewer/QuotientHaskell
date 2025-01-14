{-# LANGUAGE GADTs #-}

module AllowUnsafeCtor where

import Language.Haskell.Liquid.ProofCombinators

{-@ type K X Y = { _:F | X = Y } @-}

{-@ LIQUID "--allow-unsafe-constructors" @-}
data F where
{-@ MkF :: x:Int -> y:Int -> K x y @-}
    MkF :: Int -> Int -> F

{-@ falseProof :: { false } @-}
falseProof = () ? MkF 0 2