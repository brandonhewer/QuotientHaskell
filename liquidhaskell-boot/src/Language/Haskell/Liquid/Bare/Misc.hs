{-# LANGUAGE FlexibleContexts         #-}


module Language.Haskell.Liquid.Bare.Misc
  ( joinVar
  , mkVarExpr
  , vmap
  , runMapTyVars
  , matchKindArgs
  , symbolRTyVar
  , simpleSymbolVar
  , hasBoolResult
  , isKind
  ) where

import           Prelude                               hiding (error)

import           Liquid.GHC.API       as Ghc  hiding (Located, get, showPpr)

import           Control.Monad                         (zipWithM_)
import           Control.Monad.Except                  (MonadError, throwError)
import           Control.Monad.State
import qualified Data.Maybe                            as Mb --(fromMaybe, isNothing)

import qualified Text.PrettyPrint.HughesPJ             as PJ
import qualified Data.List                             as L
import qualified Language.Fixpoint.Types as F
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.Types

-- import           Language.Haskell.Liquid.Bare.Env

-- import           Language.Haskell.Liquid.WiredIn       (dcPrefix)


-- TODO: This is where unsorted stuff is for now. Find proper places for what follows.

{-
-- WTF does this function do?
makeSymbols :: (Id -> Bool) -> [Id] -> [F.Symbol] -> BareM [(F.Symbol, Var)]
makeSymbols f vs xs
  = do svs <- M.toList <$> gets varEnv
       return $ L.nub ([ (x,v') | (x,v) <- svs, x `elem` xs, let (v',_,_) = joinVar vs (v,x,x)]
                   ++  [ (F.symbol v, v) | v <- vs, f v, isDataConId v, hasBasicArgs $ varType v ])
    where
      -- arguments should be basic so that autogenerated singleton types are well formed
      hasBasicArgs (ForAllTy _ t) = hasBasicArgs t
      hasBasicArgs (FunTy _ tx t)   = isBaseTy tx && hasBasicArgs t
      hasBasicArgs _              = True

-}

{-
HEAD
freeSymbols :: (Reftable r, Reftable r1, F.Reftable r2, TyConable c, TyConable c1, TyConable c2)
            => [F.Symbol]
            -> [(a1, Located (RType c2 tv2 r2))]
            -> [(a, Located (RType c1 tv1 r1))]
            -> [Located (RType c tv r)]
            -> [LocSymbol]
freeSymbols xs' xts yts ivs =  [ lx | lx <- Misc.sortNub $ zs ++ zs' ++ zs'' , not (M.member (val lx) knownM) ]
  where
    knownM                  = M.fromList [ (x, ()) | x <- xs' ]
    zs                      = concatMap freeSyms (snd <$> xts)
    zs'                     = concatMap freeSyms (snd <$> yts)
    zs''                    = concatMap freeSyms ivs



-------------------------------------------------------------------------------
freeSyms :: (Reftable r, TyConable c) => Located (RType c tv r) -> [LocSymbol]
-------------------------------------------------------------------------------
freeSyms ty    = [ F.atLoc ty x | x <- tySyms ]
  where
    tySyms     = Misc.sortNub $ concat $ efoldReft (\_ _ -> True) False (\_ _ -> []) (const []) (const ()) f (const id) F.emptySEnv [] (val ty)
    f γ _ r xs = let F.Reft (v, _) = toReft r in
                 [ x | x <- F.syms r, x /= v, not (x `F.memberSEnv` γ)] : xs

--- ABOVE IS THE T1773 STUFF
--- BELOW IS THE develop-classes STUFF

-- freeSymbols :: (Reftable r, Reftable r1, F.Reftable r2, TyConable c, TyConable c1, TyConable c2)
--             => [F.Symbol]
--             -> [(a1, Located (RType c2 tv2 r2))]
--             -> [(a, Located (RType c1 tv1 r1))]
--             -> [(Located (RType c tv r))]
--             -> [LocSymbol]
-- freeSymbols xs' xts yts ivs =  [ lx | lx <- Misc.sortNub $ zs ++ zs' ++ zs'' , not (M.member (val lx) knownM) ]
--   where
--     knownM                  = M.fromList [ (x, ()) | x <- xs' ]
--     zs                      = concatMap freeSyms (snd <$> xts)
--     zs'                     = concatMap freeSyms (snd <$> yts)
--     zs''                    = concatMap freeSyms ivs



-- freeSyms :: (Reftable r, TyConable c) => Located (RType c tv r) -> [LocSymbol]
-- freeSyms ty    = [ F.atLoc ty x | x <- tySyms ]
--   where
--     tySyms     = Misc.sortNub $ concat $ efoldReft (\_ _ -> True) False (\_ _ -> []) (\_ -> []) (const ()) f (const id) F.emptySEnv [] (val ty)
--     f γ _ r xs = let F.Reft (v, _) = toReft r in
--                  [ x | x <- F.syms r, x /= v, not (x `F.memberSEnv` γ)] : xs

-}
-------------------------------------------------------------------------------
-- Renaming Type Variables in Haskell Signatures ------------------------------
-------------------------------------------------------------------------------
runMapTyVars :: Bool -> Type -> SpecType -> (PJ.Doc -> PJ.Doc -> Error) -> Either Error MapTyVarST
runMapTyVars allowTC τ t err = execStateT (mapTyVars allowTC τ t) (MTVST [] err)

data MapTyVarST = MTVST
  { vmap   :: [(Var, RTyVar)]
  , errmsg :: PJ.Doc -> PJ.Doc -> Error
  }

mapTyVars :: Bool -> Type -> SpecType -> StateT MapTyVarST (Either Error) ()
mapTyVars allowTC (FunTy { ft_arg = τ, ft_res = τ'}) t
  | isErasable τ
  = mapTyVars allowTC τ' t
  where isErasable = if allowTC then isEmbeddedDictType else isClassPred
mapTyVars allowTC (FunTy { ft_arg = τ, ft_res = τ'}) (RFun _ _ t t' _)
   = mapTyVars allowTC τ t >> mapTyVars allowTC τ' t'
mapTyVars allowTC τ (RAllT _ t _)
  = mapTyVars allowTC τ t
mapTyVars allowTC (TyConApp _ τs) (RApp _ ts _ _)
   = zipWithM_ (mapTyVars allowTC) τs (matchKindArgs' τs ts)
mapTyVars _ (TyVarTy α) (RVar a _)
   = do s  <- get
        s' <- mapTyRVar α a s
        put s'
mapTyVars allowTC τ (RAllP _ t)
  = mapTyVars allowTC τ t
mapTyVars allowTC τ (RAllE _ _ t)
  = mapTyVars allowTC τ t
mapTyVars allowTC τ (RChooseQ _ _ _ t)
  = mapTyVars allowTC τ t
mapTyVars allowTC τ (RQuotient t _)
  = mapTyVars allowTC τ t
mapTyVars allowTC τ (RRTy _ _ _ t)
  = mapTyVars allowTC τ t
mapTyVars allowTC τ (REx _ _ t)
  = mapTyVars allowTC τ t
mapTyVars _ _ (RExprArg _)
  = return ()
mapTyVars allowTC (AppTy τ τ') (RAppTy t t' _)
  = do  mapTyVars allowTC τ t
        mapTyVars allowTC τ' t'
mapTyVars _ _ (RHole _)
  = return ()
mapTyVars _ k _ | isKind k
  = return ()
mapTyVars allowTC (ForAllTy _ τ) t
  = mapTyVars allowTC τ t
mapTyVars _ hsT lqT
  = do err <- gets errmsg
       throwError (err (F.pprint hsT) (F.pprint lqT))

isKind :: Kind -> Bool
isKind = isTYPEorCONSTRAINT -- TODO:GHC-863 isStarKind k --  typeKind k


mapTyRVar :: MonadError Error m
          => Var -> RTyVar -> MapTyVarST -> m MapTyVarST
mapTyRVar α a s@(MTVST αas err)
  = case lookup α αas of
      Just a' | a == a'   -> return s
              | otherwise -> throwError (err (F.pprint a) (F.pprint a'))
      Nothing             -> return $ MTVST ((α,a):αas) err

matchKindArgs' :: [Type] -> [SpecType] -> [SpecType]
matchKindArgs' ts1' = reverse . go (reverse ts1') . reverse
  where
    go (_:ts1) (t2:ts2) = t2:go ts1 ts2
    go ts      []       | all isKind ts
                        = (ofType <$> ts) :: [SpecType]
    go _       ts       = ts


matchKindArgs :: [SpecType] -> [SpecType] -> [SpecType]
matchKindArgs ts1' = reverse . go (reverse ts1') . reverse
  where
    go (_:ts1) (t2:ts2) = t2:go ts1 ts2
    go ts      []       = ts
    go _       ts       = ts

mkVarExpr :: Id -> F.Expr
mkVarExpr v
  | isFunVar v = F.mkEApp (varFunSymbol v) []
  | otherwise  = F.eVar v -- EVar (symbol v)

varFunSymbol :: Id -> Located F.Symbol
varFunSymbol = dummyLoc . F.symbol . idDataCon

isFunVar :: Id -> Bool
isFunVar v   = isDataConId v && not (null αs) && Mb.isNothing tf
  where
    (αs, t)  = splitForAllTyCoVars $ varType v
    tf       = splitFunTy_maybe t

-- the Vars we lookup in GHC don't always have the same tyvars as the Vars
-- we're given, so return the original var when possible.
-- see tests/pos/ResolvePred.hs for an example
joinVar :: [Var] -> (Var, s, t) -> (Var, s, t)
joinVar vs (v,s,t) = case L.find ((== showPpr v) . showPpr) vs of
                       Just v' -> (v',s,t)
                       Nothing -> (v,s,t)

simpleSymbolVar :: Var -> F.Symbol
simpleSymbolVar  = dropModuleNames . F.symbol . showPpr . getName

hasBoolResult :: Type -> Bool
hasBoolResult (ForAllTy _ t) = hasBoolResult t
hasBoolResult (FunTy { ft_res = t} )    | eqType boolTy t = True
hasBoolResult (FunTy { ft_res = t} )    = hasBoolResult t
hasBoolResult _              = False
