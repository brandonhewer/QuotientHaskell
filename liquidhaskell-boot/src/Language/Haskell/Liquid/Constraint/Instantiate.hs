{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Haskell.Liquid.Constraint.Instantiate
  ( Instantiated (..)
  , Quantified   (..)
  , QVarInst
  , TypeInst
  , freshInstType
  , instantiate
  , instQVFromList
  , instTVFromList
  ) where

import           Control.Monad                                  (foldM)
import           Data.Foldable                                  (foldrM)
import           Data.Functor                                   (void, ($>))
import qualified Data.HashMap.Internal                           as HashMapI
import qualified Data.HashMap.Strict                            as HashMap
import           Data.HashMap.Strict                            (HashMap)
import qualified Data.Maybe                                     as Maybe

import           Language.Fixpoint.Types                        (Expr, Symbol)
import qualified Language.Fixpoint.Types                        as Fixpoint
import           Language.Haskell.Liquid.Constraint.Env         ((+=))
import qualified Language.Haskell.Liquid.Constraint.Fresh       as Fresh
import qualified Language.Haskell.Liquid.Constraint.Monad       as Constraint
import           Language.Haskell.Liquid.Constraint.Types       (CG, CGEnv)
import qualified Language.Haskell.Liquid.Constraint.Types       as Constraint
import           Language.Haskell.Liquid.Constraint.Unification (UnifyTypeRep)
import qualified Language.Haskell.Liquid.Constraint.Unification as Unification
import qualified Language.Haskell.Liquid.Types.PredType         as Liquid
import qualified Language.Haskell.Liquid.Types.RefType          as Liquid
import           Language.Haskell.Liquid.Types.RType
  ( PVar
  , QVarKind
  , RReft
  , RSort
  , RTVU
  , RTyCon
  , RTyVar
  , SpecProp
  , SpecQVar
  , SpecType
  )
import qualified Language.Haskell.Liquid.Types.RTypeOp          as Liquid
import           Language.Haskell.Liquid.Types.AntiUnify        (AUTypeRep)
import qualified Language.Haskell.Liquid.Types.AntiUnify        as AntiUnify
import qualified Language.Haskell.Liquid.Types.Fresh            as Fresh
import qualified Language.Haskell.Liquid.Types.QuotSubst        as Quotient
import qualified Language.Haskell.Liquid.Types.RType            as Liquid
import qualified Language.Haskell.Liquid.Types.Types            as Liquid
import qualified Language.Haskell.Liquid.UX.Config              as Config

type SpecTypeRep = UnifyTypeRep RTyCon RTyVar RReft
type SpecAUType  = AUTypeRep Symbol RTyCon RTyVar ()

data Instantiated
  = Instantiated
      { instTVs  :: !(HashMap RTyVar TypeInst)
      , instQVs  :: !(HashMap Symbol QVarInst)
      , instType :: !SpecType
      }

data Quantified
  = Quantified
      { typeVars :: ![(RTyVar, RReft)]
      , quotVars :: ![(SpecQVar, RReft)]
      , baseType :: !SpecType
      }

data QuotInst
  = QInstVar  !RReft
  | QInstType !SpecType

data TypeInst
  = InstVar  !RReft
  | InstType !SpecTypeRep

data QVarInst
  = QVarInst
      { quotInst :: !QuotInst
      , quotKind :: !QVarKind
      , quotType :: !SpecAUType
      }

instTVFromList :: [(RTVU RTyCon RTyVar, RReft)] -> HashMap RTyVar TypeInst
instTVFromList αs = HashMap.fromList [ (Liquid.ty_var_value α, InstVar r) | (α, r) <- αs ]

instQVFromList :: [(SpecQVar, RReft)] -> HashMap Symbol QVarInst
instQVFromList qs
  = HashMap.fromList
      [ (q, qvar)
      | (Liquid.QVar {..}, r) <- qs
      , let qvar
              = QVarInst
                  { quotInst = QInstVar r
                  , quotKind = qv_kind
                  , quotType = AntiUnify.toAUTypeRep qv_type
                  }
      , q <- qv_quotient : qv_quotients
      ]

-----------------------------------------------------------------------
-- | Creating Fresh Refinements         -------------------------------
-----------------------------------------------------------------------
supportTypeclass :: CGEnv -> Bool
supportTypeclass = Config.typeclass . Config.getConfig

freshPredBody :: CGEnv -> RSort -> CG SpecType
freshPredBody γ
  = Fresh.freshTyReftype (supportTypeclass γ) Liquid.PredInstE
  . Liquid.ofType
  . Liquid.toType False

freshPredArgs :: [(RSort, Symbol, Expr)] -> CG [(Symbol, RSort)]
freshPredArgs as = makeArgs <$> traverse (const Fresh.fresh) as
  where
    makeArgs args = [(x, s) | (x, (s, y, z)) <- zip args as, Fixpoint.EVar y == z ]

freshPredRef :: CGEnv -> PVar RSort -> CG SpecProp
freshPredRef γ (Liquid.PV _ rsort _ as) = do
  rf_body <- freshPredBody γ rsort
  rf_args <- freshPredArgs as
  γ' <- foldM (+=) γ [("freshPredRef", x, Liquid.ofRSort τ) | (x, τ) <- rf_args]
  Constraint.addW (Constraint.WfC γ' rf_body) $> Liquid.RProp {..}

freshInstType :: CGEnv -> SpecType -> CG Instantiated
freshInstType γ τ
  = go Instantiated
      { instTVs  = HashMap.empty
      , instQVs  = HashMap.empty
      , instType = τ
      } 
  where
    go :: Instantiated -> CG Instantiated
    go i@Instantiated {..}
      = case instType of
          Liquid.RAllT {..} -> do
            let tv = Liquid.ty_var_value rt_tvbind
            α <- Fresh.fresh
            go i
              { instType = Liquid.subsTyVarMeet' (tv, Liquid.RVar α mempty) rt_ty
              , instTVs  = HashMapI.unsafeInsert α (InstVar rt_ref) instTVs
              }

          Liquid.RChooseQ {..}
            | Liquid.ForAllQ <- Liquid.qv_kind rt_qvbind -> do
                let oq = Liquid.qv_quotient rt_qvbind
                q <- Fresh.fresh
                go i
                  { instType = Quotient.renameQVs (HashMap.singleton oq q) rt_ty
                  , instQVs
                      = HashMapI.unsafeInsert q QVarInst
                          { quotInst = QInstVar rt_reft
                          , quotKind = Liquid.qv_kind rt_qvbind
                          , quotType = AntiUnify.toAUTypeRep $ Liquid.qv_type rt_qvbind
                          } instQVs
                  }
            | otherwise -> do
                let mkResult q0 r = addQuotVar q0 r <$> Fresh.fresh
                    oq            = Liquid.qv_quotient rt_qvbind
                q <- Fresh.fresh
                mkInstantiated
                  <$> foldrM mkResult
                        ( HashMap.singleton oq q
                        , HashMapI.unsafeInsert q quotVar instQVs
                        ) (Liquid.qv_quotients rt_qvbind)
            where
              quotVar
                = QVarInst
                    { quotInst = QInstVar rt_reft
                    , quotType = AntiUnify.toAUTypeRep $ Liquid.qv_type rt_qvbind
                    , quotKind = Liquid.qv_kind rt_qvbind
                    }

              addQuotVar q0 (renaming', σ') nq
                = ( HashMapI.unsafeInsert q0 nq renaming'
                  , HashMapI.unsafeInsert nq quotVar σ'
                  )

              mkInstantiated (renaming, nquotVars)
                = i { instType = Quotient.renameQVs renaming rt_ty
                    , instQVs  = nquotVars
                    }

          Liquid.RAllP {..} -> mkInstantiated <$> freshPredRef γ rt_pvbind
            where
              mkInstantiated p
                = i { instType = Liquid.replacePreds "consE" instType [(rt_pvbind, p)]
                    }

          _ -> pure i

-----------------------------------------------------------------------
-- | Partitioning instantiations         ------------------------------
-----------------------------------------------------------------------
getInstVar :: RTyVar -> TypeInst -> Maybe (RTyVar, RReft)
getInstVar α (InstVar r) = Just (α, r)
getInstVar _ _           = Nothing

getInstType :: TypeInst -> Maybe SpecType
getInstType (InstVar _)  = Nothing
getInstType (InstType τ) = Just $ Unification.fromUnifyTypeRep τ

getQInstVar :: (RSort -> RSort) -> Symbol -> QVarInst -> Maybe (SpecQVar, RReft)
getQInstVar f qv_quotient QVarInst {..}
  | QInstVar r <- quotInst
      = Just
          ( Liquid.QVar
              { qv_quotients = []
              , qv_kind      = quotKind
              , qv_type      = f $ AntiUnify.fromAUTypeRep quotType
              , ..
              }
          , r
          )
  | otherwise = Nothing

getQInstType :: QuotInst -> Maybe SpecType
getQInstType (QInstVar _)  = Nothing
getQInstType (QInstType τ) = Just τ

instantiate :: Instantiated -> Quantified
instantiate Instantiated {..}
  | HashMap.null τσ && isNullQσ
      = Quantified
          { baseType = instType
          , quotVars = Maybe.mapMaybe (uncurry $ getQInstVar id) listQVs
          , ..
          }
  | otherwise
      = Quantified
          { baseType = instantiate' τσ qσ instType
          , quotVars = Maybe.mapMaybe (uncurry $ applyQV τσ) listQVs
          , ..
          }
  where
    τσ        = HashMap.mapMaybe getInstType instTVs
    qσ        = HashMap.mapMaybe (getQInstType . quotInst) instQVs
    isNullQσ  = HashMap.null qσ
    typeVars  = Maybe.mapMaybe (uncurry getInstVar) (HashMap.toList instTVs)
    listQVs   = HashMap.toList instQVs
    applyQV σ = getQInstVar $ if isNullQσ then id else instantiateQV σ

instantiateQV :: HashMap RTyVar SpecType -> RSort -> RSort
instantiateQV τσ = go
  where
    go τ@Liquid.RVar {..}
      | Just τ' <- HashMap.lookup rt_var τσ = void τ' `Liquid.strengthen` rt_reft
      | otherwise                           = τ

    go τ@Liquid.RFun {rt_in, rt_out}
      = τ { Liquid.rt_in  = go rt_in
          , Liquid.rt_out = go rt_out
          }

    go τ@Liquid.RAllT {rt_ty}
      = τ { Liquid.rt_ty = go rt_ty
          }
  
    go τ@Liquid.RAllP {rt_ty}
      = τ { Liquid.rt_ty = go rt_ty
          }

    go τ@Liquid.RChooseQ {rt_ty}
      = τ { Liquid.rt_ty = go rt_ty
          }

    go τ@Liquid.RQuotient {rt_ty}
      = τ { Liquid.rt_ty = go rt_ty
          }

    go τ@Liquid.RApp {rt_args}
      = τ { Liquid.rt_args = map go rt_args
          }

    go τ@Liquid.RAllE {rt_allarg, rt_ty}
      = τ { Liquid.rt_allarg = go rt_allarg
          , Liquid.rt_ty     = go rt_ty
          }

    go τ@Liquid.REx {rt_exarg, rt_ty}
      = τ { Liquid.rt_exarg = go rt_exarg
          , Liquid.rt_ty    = go rt_ty
          }

    go τ@Liquid.RExprArg {} = τ

    go τ@Liquid.RAppTy {rt_arg, rt_res}
      = τ { Liquid.rt_arg = go rt_arg
          , Liquid.rt_res = go rt_res
          }

    go τ@Liquid.RRTy {rt_env, rt_ty}
      = τ { Liquid.rt_env = map (fmap go) rt_env
          , Liquid.rt_ty  = go rt_ty
          }

    go τ@Liquid.RHole {} = τ

-- | Instantiation function that assumes that every type and quotient variable in the
--   the provided substitution maps are NOT bound in the type.
instantiate' :: HashMap RTyVar SpecType -> HashMap Symbol SpecType -> SpecType -> SpecType
instantiate' τσ qσ = go
  where
    go τ@Liquid.RVar {..}
      | Just τ' <- HashMap.lookup rt_var τσ = τ' `Liquid.strengthen` rt_reft
      | otherwise                           = τ

    go τ@Liquid.RFun {rt_in, rt_out}
      = τ { Liquid.rt_in  = go rt_in
          , Liquid.rt_out = go rt_out
          }

    go τ@Liquid.RAllT {rt_ty}
      = τ { Liquid.rt_ty = go rt_ty
          }
  
    go τ@Liquid.RAllP {rt_ty}
      = τ { Liquid.rt_ty = go rt_ty
          }

    go τ@Liquid.RChooseQ {rt_ty}
      = τ { Liquid.rt_ty = go rt_ty
          }

    go τ@Liquid.RQuotient {rt_ty, rt_quotient}
      | Just τ' <- HashMap.lookup rt_quotient qσ = go τ'
      | otherwise                                = τ { Liquid.rt_ty = go rt_ty }

    go τ@Liquid.RApp {rt_args}
      = τ { Liquid.rt_args = map go rt_args
          }

    go τ@Liquid.RAllE {rt_allarg, rt_ty}
      = τ { Liquid.rt_allarg = go rt_allarg
          , Liquid.rt_ty     = go rt_ty
          }

    go τ@Liquid.REx {rt_exarg, rt_ty}
      = τ { Liquid.rt_exarg = go rt_exarg
          , Liquid.rt_ty    = go rt_ty
          }

    go τ@Liquid.RExprArg {} = τ

    go τ@Liquid.RAppTy {rt_arg, rt_res}
      = τ { Liquid.rt_arg = go rt_arg
          , Liquid.rt_res = go rt_res
          }

    go τ@Liquid.RRTy {rt_env, rt_ty}
      = τ { Liquid.rt_env = map (fmap go) rt_env
          , Liquid.rt_ty  = go rt_ty
          }

    go τ@Liquid.RHole {} = τ


subsumes :: Quantified -> SpecType -> Either (SpecType, SpecType) (HashMap Symbol SpecType)
subsumes Quantified {..} rτ = go baseType rτ
  where
    go Liquid.RVar {..} τ' = x
