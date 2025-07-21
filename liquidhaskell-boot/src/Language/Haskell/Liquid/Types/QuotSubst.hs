{-# LANGUAGE NamedFieldPuns #-}

module Language.Haskell.Liquid.Types.QuotSubst
  ( substitute
  ) where

import           Data.HashMap.Strict                 (HashMap)
import qualified Data.HashMap.Strict                 as HashMap

import           Language.Fixpoint.Types             (Symbol)
import qualified Language.Fixpoint.Types             as Fixpoint
import           Language.Haskell.Liquid.Types.RType (RTyCon, RTypeV (..), RTyVar, SpecType)

substitute
  :: HashMap Symbol (RTypeV v RTyCon RTyVar r)
  -> SpecType
  -> RTypeV v RTyCon RTyVar r
substitute σ RVar {..}
  | Just t <- HashMap.lookup var σ = t
  | otherwise                      = y
  where
    var :: Symbol
    var = Fixpoint.symbol rt_var

{-
RVar {
      rt_var    :: !tv
    , rt_reft   :: !r
    }

  | RFun  {
      rt_bind   :: !Symbol
    , rt_rinfo  :: !RFInfo
    , rt_in     :: !(RTypeV v c tv r)
    , rt_out    :: !(RTypeV v c tv r)
    , rt_reft   :: !r
    }

  | RAllT {
      rt_tvbind :: !(RTVUV v c tv) -- RTVar tv (RType c tv ()))
    , rt_ty     :: !(RTypeV v c tv r)
    , rt_ref    :: !r
    }

  -- | "forall x y <z :: Nat, w :: Int> . TYPE"
  --               ^^^^^^^^^^^^^^^^^^^ (rt_pvbind)
  | RAllP {
      rt_pvbind :: !(PVUV v c tv)
    , rt_ty     :: !(RTypeV v c tv r)
    }

  -- | For example "choose q :: []. (a -> b) -> [a] / q -> [b] / q"
  -- |                          ^^ rt_qty
  | RChooseQ {
      rt_quotient  :: !Symbol
    , rt_quotients :: [Symbol]
    , rt_qty       :: !(RTypeV v c tv r)
    , rt_ty        :: !(RTypeV v c tv r)
    }

  -- | For example "[a] / q"
  --                      ^ rt_quotient
  | RQuotient {
      rt_ty       :: !(RTypeV v c tv r)
    , rt_quotient :: !Symbol
    }

  -- | For example, in [a]<{\h -> v > h}>, we apply (via `RApp`)
  --   * the `RProp`  denoted by `{\h -> v > h}` to
  --   * the `RTyCon` denoted by `[]`.
  | RApp  {
      rt_tycon  :: !c
    , rt_args   :: ![RTypeV v c tv r]
    , rt_pargs  :: ![RTPropV v c tv r]
    , rt_reft   :: !r
    }

  | RAllE {
      rt_bind   :: !Symbol
    , rt_allarg :: !(RTypeV v c tv r)
    , rt_ty     :: !(RTypeV v c tv r)
    }

  | REx {
      rt_bind   :: !Symbol
    , rt_exarg  :: !(RTypeV v c tv r)
    , rt_ty     :: !(RTypeV v c tv r)
    }

  | RExprArg (F.Located (ExprV v))              -- ^ For expression arguments to type aliases
                                                --   see tests/pos/vector2.hs
  | RAppTy{
      rt_arg   :: !(RTypeV v c tv r)
    , rt_res   :: !(RTypeV v c tv r)
    , rt_reft  :: !r
    }

  | RRTy  {
      rt_env   :: ![(Symbol, RTypeV v c tv r)]
    , rt_ref   :: !r
    , rt_obl   :: !Oblig
    , rt_ty    :: !(RTypeV v c tv r)
    }

  | RHole r -- ^ let LH match against the Haskell type and add k-vars, e.g. `x:_`
            --   see tests/pos/Holes.hs
-}
