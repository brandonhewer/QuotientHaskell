module Language.Haskell.Liquid.GHC.CoreToLogic where

coreToLogic :: String
coreToLogic = unlines
  [ "define GHC.Types.True                   = (true)"
  , "define GHC.Classes.not x                = (~ x)"
  , "define GHC.Internal.Base.$ f x          = (f x)"
  , "define Main.mempty       = (mempty)"
  , "define Control.Parallel.Strategies.withStrategy s x = (x)"
  , "define Language.Haskell.Liquid.Equational.eq x y = (y)"
  , "define Language.Haskell.Liquid.ProofCombinators.cast x y = (y)"
  , "define Liquid.ProofCombinators.cast x y = (y)"
  , "define ProofCombinators.cast x y = (y)"
  ]
