{-@ LIQUID "--save" @-}
module WithProofRefl where

import Language.Haskell.Liquid.ProofCombinators

{-@ reflect unify' @-}
unify' :: Int -> Int
unify' 0 = 42
unify' i = (i-1) `withProof` theoremUnify' i

theoremUnify' :: Int -> Proof
theoremUnify' i = ()
-- theoremUnify' i = theoremUnify' (i-1)
