{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.Internal.Base_LHAssumptions where

import GHC.Base (assert)
import GHC.CString_LHAssumptions()
import GHC.Exts_LHAssumptions()
import GHC.Types_LHAssumptions()
import Data.Tuple_LHAssumptions()

{-@

assume . :: forall <p :: b -> c -> Bool, q :: a -> b -> Bool, r :: a -> c -> Bool>.
                   {xcmp::a, wcmp::b<q xcmp> |- c<p wcmp> <: c<r xcmp>}
                   (ycmp:b -> c<p ycmp>)
                -> (zcmp:a -> b<q zcmp>)
                ->  xcmp:a -> c<r xcmp>

measure autolen :: forall a. a -> Int

//  Useless as compiled into GHC primitive, which is ignored
assume assert :: {v:Bool | v } -> a -> a

instance measure len :: forall a. [a] -> Int
  len []     = 0
  len (y:ys) = 1 + len ys

invariant {v: [a] | len v >= 0 }
assume map       :: (a -> b) -> xs:[a] -> {v: [b] | len v == len xs}
assume ++        :: xs:[a] -> ys:[a] -> {v:[a] | len v == len xs + len ys}

assume $         :: (a -> b) -> a -> b
assume id        :: x:a -> {v:a | v = x}

qualif IsEmp(v:Bool, xs: [a]) : (v <=> (len xs > 0))
qualif IsEmp(v:Bool, xs: [a]) : (v <=> (len xs = 0))

qualif ListZ(v: [a])          : (len v =  0)
qualif ListZ(v: [a])          : (len v >= 0)
qualif ListZ(v: [a])          : (len v >  0)

qualif CmpLen(v:[a], xs:[b])  : (len v  =  len xs )
qualif CmpLen(v:[a], xs:[b])  : (len v  >= len xs )
qualif CmpLen(v:[a], xs:[b])  : (len v  >  len xs )
qualif CmpLen(v:[a], xs:[b])  : (len v  <= len xs )
qualif CmpLen(v:[a], xs:[b])  : (len v  <  len xs )

qualif EqLen(v:int, xs: [a])  : (v = len xs )
qualif LenEq(v:[a], x: int)   : (x = len v )

qualif LenDiff(v:[a], x:int)  : (len v  = x + 1)
qualif LenDiff(v:[a], x:int)  : (len v  = x - 1)
qualif LenAcc(v:int, xs:[a], n: int): (v = len xs  + n)

@-}
