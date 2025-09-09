{-# LANGUAGE NamedFieldPuns #-}

module Language.Haskell.Liquid.Types.Renaming
  ( rename
  ) where

import           Language.Fixpoint.Types             (Symbol)
import           Language.Haskell.Liquid.Types.RType (RTypeV)
import qualified Language.Haskell.Liquid.Types.RType as Liquid

-- | Renaming function on refinement types that assume every renaming is fresh.
rename :: (Symbol -> Symbol) -> (tv -> tv) -> RTypeV v c tv r -> RTypeV v c tv r
rename _ σTV τ@Liquid.RVar {rt_var} = τ { Liquid.rt_var = σTV rt_var }
rename σQV σTV τ@Liquid.RFun {rt_in, rt_out}
  = τ { Liquid.rt_in  = rename σQV σTV rt_in
      , Liquid.rt_out = rename σQV σTV rt_out
      }
rename σQV σTV τ@Liquid.RAllT {rt_tvbind, rt_ty}
  = τ { Liquid.rt_tvbind = rename σQV σTV <$> rt_tvbind
      , Liquid.rt_ty     = rename σQV σTV rt_ty
      }
rename σQV σTV τ@Liquid.RAllP {rt_pvbind, rt_ty}
  = τ { Liquid.rt_pvbind = rename σQV σTV <$> rt_pvbind
      , Liquid.rt_ty     = rename σQV σTV rt_ty
      }
rename σQV σTV τ@Liquid.RChooseQ {rt_qvbind, rt_ty}
  = τ { Liquid.rt_qvbind = rename σQV σTV <$> rt_qvbind
      , Liquid.rt_ty     = rename σQV σTV rt_ty
      }
rename σQV σTV τ@Liquid.RQuotient {rt_ty, rt_quotient}
  = τ { Liquid.rt_quotient = σQV rt_quotient
      , Liquid.rt_ty       = rename σQV σTV rt_ty
      }
rename σQV σTV τ@Liquid.RApp {rt_args, rt_pargs}
  = τ { Liquid.rt_args  = map (rename σQV σTV) rt_args
      , Liquid.rt_pargs = map (rename σQV σTV <$>) rt_pargs
      }
rename σQV σTV τ@Liquid.RAllE {rt_allarg, rt_ty}
  = τ { Liquid.rt_allarg = rename σQV σTV rt_allarg
      , Liquid.rt_ty     = rename σQV σTV rt_ty
      }
rename σQV σTV τ@Liquid.REx {rt_exarg, rt_ty}
  = τ { Liquid.rt_exarg = rename σQV σTV rt_exarg
      , Liquid.rt_ty    = rename σQV σTV rt_ty
      }
rename _ _ τ@Liquid.RExprArg {} = τ
rename σQV σTV τ@Liquid.RAppTy {rt_arg, rt_res}
  = τ { Liquid.rt_arg = rename σQV σTV rt_arg
      , Liquid.rt_res = rename σQV σTV rt_res
      }
rename σQV σTV τ@Liquid.RRTy {rt_env, rt_ty}
  = τ { Liquid.rt_env = map (rename σQV σTV <$>) rt_env
      , Liquid.rt_ty  = rename σQV σTV rt_ty
      }
rename _ _ τ@Liquid.RHole {} = τ
