{-# Language GADTs #-}

{-@ LIQUID "--expect-any-error" @-}

module RefinedProp where

import Language.Haskell.Liquid.ProofCombinators

data Id where
{-@ MkId :: Prop (Id 12) @-}
    MkId :: Id
data ID = Id Int

-- Should error as False is supposed to not be satisfied
{-@ bad :: { v:Prop (Id 12) | False } @-}
bad = MkId