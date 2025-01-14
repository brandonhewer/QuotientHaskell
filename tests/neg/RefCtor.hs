{-# LANGUAGE GADTs #-}

-- | Tests that the returned refinement type of data constructors
-- is not allowed to be other than @True@.
module RefCtor where

import Language.Haskell.Liquid.ProofCombinators

{-@ type K X Y = { _:F | X = Y } @-}

data F where
{-@ LIQUID "--expect-error-containing=Refinement of the data constructor RefCtor.MkF doesn't admit an arbitrary refinements on the return type" @-}
{-@ MkF :: x:Int -> y:Int -> K x y @-}
    MkF :: Int -> Int -> F

{-@ falseProof :: { false } @-}
falseProof = () ? MkF 0 2