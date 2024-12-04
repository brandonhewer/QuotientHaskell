{-@ LIQUID "--expect-error-containing=Unknown variable `goober`" @-}
module MissingAssume where

import qualified Data.Set

{-@ type UList a = {v:[a] | ListUnique v} @-}

{-@ assume goober :: Nat -> Nat @-} 

{-@ assume reverse :: xs:(UList a) -> {v: UList a | EqElts v xs}  @-}

{-@ predicate ListUnique LS = (Set_emp (listDup LS)) @-}

{-@ predicate EqElts X Y    = ((Data.Set.listElts X) = (Data.Set.listElts Y)) @-}

{-@
  measure listDup :: [a] -> (Data.Set.Set a)
    listDup []    = {v | Set_emp v }
    listDup (x:xs) = {v | v = if (Set_mem x (Data.Set.listElts xs)) then (Set_cup (Set_sng x) (listDup xs)) else (listDup xs) }
  @-}

{-@ foo :: xs:(UList a) -> {v: UList a | EqElts v xs} @-}
foo  = reverse 
