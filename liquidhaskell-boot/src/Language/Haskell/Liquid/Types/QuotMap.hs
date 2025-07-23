{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE NamedFieldPuns #-}

module Language.Haskell.Liquid.Types.QuotMap
  ( emapQuotDeclM
  , mapQuotDeclV
  , mapEqualityCtorV
  , mapEqualityParamV
  ) where

import           Control.Monad.State.Strict             (StateT)
import qualified Control.Monad.State.Strict             as State

import           Language.Fixpoint.Types                (Symbol)

import           Language.Haskell.Liquid.Types.QuotDecl
  ( EqualityCtorP
  , EqualityParamP
  , QuotDeclP
  )
import qualified Language.Haskell.Liquid.Types.QuotDecl as Quotient
import qualified Language.Haskell.Liquid.Types.RType    as Liquid
import qualified Language.Haskell.Liquid.Types.RTypeOp  as Liquid

emapQuotDeclM
  :: Monad m
  => Bool
  -> ([Symbol] -> v -> m v')
  -> ([Symbol] -> v -> m v')
  -> ([Symbol] -> ty -> m ty')
  -> QuotDeclP v ty
  -> m (QuotDeclP v' ty')
emapQuotDeclM bscp vf ef f q
  = makeQuotientDecl
      <$> traverse (Liquid.emapPVarVM vf (Liquid.emapReftM bscp vf (const pure))) (Quotient.qtycPVars q)
      <*> traverse (f $ Quotient.qtycTyVars q) (Quotient.qtycType q)
      <*> emapEqualityCtorM ef f (Quotient.qtycTyVars q) (Quotient.qtycFirstEqCon q)
      <*> traverse (emapEqualityCtorM ef f $ Quotient.qtycTyVars q) (Quotient.qtycEqCons q)
      <*> traverse (traverse (vf [])) (Quotient.qtycSFun q)
  where
    makeQuotientDecl qtycPVars qtycType qtycFirstEqCon qtycEqCons qtycSFun
      = q { Quotient.qtycPVars
          , Quotient.qtycType
          , Quotient.qtycFirstEqCon
          , Quotient.qtycEqCons
          , Quotient.qtycSFun
          }

emapEqualityCtorM
  :: Monad m
  => ([Symbol] -> v -> m v')
  -> ([Symbol] -> ty -> m ty')
  -> [Symbol]
  -> EqualityCtorP v ty
  -> m (EqualityCtorP v' ty')
emapEqualityCtorM vf f tvs ec = do
  (ecParameters, bs) <-
    State.runStateT (traverse (emapEqualityParamM vf f) $ Quotient.ecParameters ec) tvs
  makeEqualityCon ecParameters
    <$> mapM (traverse $ f tvs) (Quotient.ecTheta ec)
    <*> Liquid.emapExprVM (vf . (++ bs)) (Quotient.ecLeftTerm ec)
    <*> Liquid.emapExprVM (vf . (++ bs)) (Quotient.ecRightTerm ec)
  where
    makeEqualityCon ecParameters ecTheta ecLeftTerm ecRightTerm
      = ec  { Quotient.ecTheta
            , Quotient.ecParameters
            , Quotient.ecLeftTerm
            , Quotient.ecRightTerm
            }

emapEqualityParamM
  :: Monad m
  => ([Symbol] -> v -> m v')
  -> ([Symbol] -> ty -> m ty')
  -> EqualityParamP v ty
  -> StateT [Symbol] m (EqualityParamP v' ty')
emapEqualityParamM _ f Quotient.EqualityBindParam {..} = do
  bs <- State.get
  State.put $ epBinder : bs
  State.lift $ Quotient.EqualityBindParam epBinder <$> traverse (f bs) epType
emapEqualityParamM vf _ (Quotient.EqualityPrecondition e) = do
  bs <- State.get
  State.lift $ Quotient.EqualityPrecondition <$> Liquid.emapExprVM (vf . (++ bs)) e

mapQuotDeclV :: (v -> v') -> QuotDeclP v ty -> QuotDeclP v' ty
mapQuotDeclV f Quotient.QuotDecl {..} =
  Quotient.QuotDecl
    { qtycPVars      = map (Liquid.mapPVarV f (Liquid.mapRTypeV f)) qtycPVars
    , qtycSFun       = fmap (fmap f) qtycSFun
    , qtycFirstEqCon = mapEqualityCtorV f qtycFirstEqCon
    , qtycEqCons     = map (mapEqualityCtorV f) qtycEqCons
    , ..
    }

mapEqualityParamV :: (v -> v') -> EqualityParamP v ty -> EqualityParamP v' ty
mapEqualityParamV f (Quotient.EqualityPrecondition e) = Quotient.EqualityPrecondition $ fmap f e
mapEqualityParamV _ Quotient.EqualityBindParam {..}   = Quotient.EqualityBindParam {..}

mapEqualityCtorV :: (v -> v') -> EqualityCtorP v ty -> EqualityCtorP v' ty
mapEqualityCtorV f Quotient.EqualityCtor {..} =
  Quotient.EqualityCtor
    { ecLeftTerm   = fmap f ecLeftTerm
    , ecRightTerm  = fmap f ecRightTerm
    , ecParameters = map (mapEqualityParamV f) ecParameters
    , ..
    }
