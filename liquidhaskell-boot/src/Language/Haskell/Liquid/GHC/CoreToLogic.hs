module Language.Haskell.Liquid.GHC.CoreToLogic where

coreToLogic :: String
coreToLogic = unlines
  [ "define Data.Set.Base.singleton x      = (Set_sng x)"
  , "define Data.Set.Base.union x y        = (Set_cup x y)"
  , "define Data.Set.Base.intersection x y = (Set_cap x y)"
  , "define Data.Set.Base.difference x y   = (Set_dif x y)"
  , "define Data.Set.Base.empty            = (Set_empty 0)"
  , "define Data.Set.Base.null x           = (Set_emp x)"
  , "define Data.Set.Base.member x xs      = (Set_mem x xs)"
  , "define Data.Set.Base.isSubsetOf x y   = (Set_sub x y)"
  , "define Data.Set.Base.fromList xs      = (listElts xs)"
  , ""
  , "define Data.Set.Internal.singleton x      = (Set_sng x)"
  , "define Data.Set.Internal.union x y        = (Set_cup x y)"
  , "define Data.Set.Internal.intersection x y = (Set_cap x y)"
  , "define Data.Set.Internal.difference x y   = (Set_dif x y)"
  , "define Data.Set.Internal.empty            = (Set_empty 0)"
  , "define Data.Set.Internal.null x           = (Set_emp x)"
  , "define Data.Set.Internal.member x xs      = (Set_mem x xs)"
  , "define Data.Set.Internal.isSubsetOf x y   = (Set_sub x y)"
  , "define Data.Set.Internal.fromList xs      = (listElts xs)"
  , ""
  , "define GHC.Internal.Real.fromIntegral x = (x)"
  , ""
  , "define GHC.Types.True                 = (true)"
  , "define GHC.Internal.Real.div x y      = (x / y)"
  , "define GHC.Internal.Real.mod x y      = (x mod y)"
  , "define GHC.Internal.Num.fromInteger x = (x)"
  , "define GHC.Num.Integer.IS x           = (x)"
  , "define GHC.Classes.not x              = (~ x)"
  , "define GHC.Internal.Base.$ f x        = (f x)"
  , ""
  , "define Language.Haskell.Liquid.Bag.get k b      = (Bag_count b k)"
  , "define Language.Haskell.Liquid.Bag.put k b      = (Bag_union b (Bag_sng k 1))"
  , "define Language.Haskell.Liquid.Bag.union a b    = (Bag_union a b)"
  , "define Language.Haskell.Liquid.Bag.unionMax a b = (Bag_union_max a b)"
  , "define Language.Haskell.Liquid.Bag.interMin a b = (Bag_inter_min a b)"
  , "define Language.Haskell.Liquid.Bag.sub a b      = (Bag_sub a b)"
  , "define Language.Haskell.Liquid.Bag.empty        = (Bag_empty 0)"
  , ""
  , "define Main.mempty       = (mempty)"
  , "define Language.Haskell.Liquid.ProofCombinators.cast x y = (y)"
  , "define Language.Haskell.Liquid.ProofCombinators.withProof x y = (x)"
  , "define ProofCombinators.cast x y = (y)"
  , "define Liquid.ProofCombinators.cast x y = (y)"
  , "define Control.Parallel.Strategies.withStrategy s x = (x)"
  , ""
  , "define Language.Haskell.Liquid.Equational.eq x y = (y)"
  , ""
  , "define GHC.CString.unpackCString# x = x"
  ]
