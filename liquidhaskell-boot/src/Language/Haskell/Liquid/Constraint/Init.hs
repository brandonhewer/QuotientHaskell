{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE NamedFieldPuns            #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverloadedStrings         #-}

-- | This module defines the representation of Subtyping and WF Constraints,
--   and the code for syntax-directed constraint generation.

module Language.Haskell.Liquid.Constraint.Init (
    initEnv ,
    initCGI,
    ) where

import           Prelude                                       hiding (error, undefined)
import           Control.Monad.State
import           Data.Maybe                                    (isNothing, fromMaybe, catMaybes, mapMaybe)
import qualified Data.HashMap.Strict                           as M
import qualified Data.HashSet                                  as S
import qualified Data.List                                     as L
import           Data.Bifunctor
import qualified Language.Fixpoint.Types                       as F

import qualified Language.Haskell.Liquid.UX.CTags              as Tg
import           Language.Haskell.Liquid.Constraint.Fresh
import           Language.Haskell.Liquid.Constraint.Env
import           Language.Haskell.Liquid.Constraint.NBETypes
import qualified Language.Haskell.Liquid.Constraint.Unify      as Unify
import           Language.Haskell.Liquid.WiredIn               (dictionaryVar)
import qualified Language.Haskell.Liquid.GHC.SpanStack         as Sp
import           Language.Haskell.Liquid.GHC.Misc             ( idDataConM, hasBaseTypeVar, isDataConId) -- dropModuleNames, simplesymbol)
import           Liquid.GHC.API               as Ghc
import           Language.Haskell.Liquid.Misc
import           Language.Fixpoint.Misc
import           Language.Haskell.Liquid.Constraint.ToFixpoint  (makeSimplify)
import           Language.Haskell.Liquid.Constraint.Types

import           Language.Haskell.Liquid.Types hiding (binds, Loc, loc, freeTyVars, Def)

--------------------------------------------------------------------------------
initEnv :: TargetInfo -> CG CGEnv
--------------------------------------------------------------------------------
initEnv info
  = do let tce   = gsTcEmbeds (gsName sp)
       let fVars = giImpVars (giSrc info)
       let dcs   = filter isConLikeId (snd <$> gsFreeSyms (gsName sp))
       let dcs'  = filter isConLikeId fVars
       defaults <- forM fVars $ \x -> fmap (x,) (trueTy allowTC $ varType x)
       dcsty    <- forM dcs   (makeDataConTypes allowTC)
       dcsty'   <- forM dcs'  (makeDataConTypes allowTC)
       (hs,f0)  <- refreshHoles allowTC $ grty info                           -- asserted refinements     (for defined vars)
       f0''     <- refreshArgs' =<< grtyTop info                      -- default TOP reftype      (for exported vars without spec)
       let f0'   = if notruetypes $ getConfig sp then [] else f0''
       f1       <- refreshArgs'   defaults                            -- default TOP reftype      (for all vars)
       f1'      <- refreshArgs' $ makeExactDc dcsty                   -- data constructors
       f2       <- refreshArgs' $ assm info                           -- assumed refinements      (for imported vars)
       f3'      <- refreshArgs' =<< recSelectorsTy info                      -- assumed refinements      (for record selectors)
       f3       <- addPolyInfo' <$> refreshArgs' (vals gsAsmSigs (gsSig sp))                 -- assumed refinedments     (with `assume`)
       f40      <- makeExactDc <$> refreshArgs' (vals gsCtors (gsData sp)) -- constructor refinements  (for measures)
       f5       <- refreshArgs' $ vals gsInSigs (gsSig sp)                   -- internal refinements     (from Haskell measures)
       fi       <- refreshArgs' $ catMaybes $ [(x,) . val <$> getMethodType mt | (x, mt) <- gsMethods $ gsSig $ giSpec info ]
       (invs1, f41) <- mapSndM refreshArgs' $ makeAutoDecrDataCons dcsty  (gsAutosize (gsTerm sp)) dcs
       (invs2, f42) <- mapSndM refreshArgs' $ makeAutoDecrDataCons dcsty' (gsAutosize (gsTerm sp)) dcs'
       let f4    = mergeDataConTypes tce (mergeDataConTypes tce f40 (f41 ++ f42)) (filter (isDataConId . fst) f2)
       let tx    = mapFst F.symbol . addRInv ialias . predsUnify sp
       f6       <- map tx . addPolyInfo' <$> refreshArgs' (vals gsRefSigs (gsSig sp))
       let bs    = (tx <$> ) <$> [f0 ++ f0' ++ fi, f1 ++ f1', f2, f3 ++ f3', f4, f5]
       modify $ \s -> s { dataConTys = f4 }
       lt1s     <- gets (F.toListSEnv . cgLits)
       let lt2s  = [ (F.symbol x, rTypeSort tce t) | (x, t) <- f1' ]
       let tcb   = mapSnd (rTypeSort tce) <$> concat bs
       let cbs   = giCbs . giSrc $ info
       rTrue   <- mapM (mapSndM (true allowTC)) f6
       let dconM = M.fromList (map (first F.symbol) f4)
       let γ0    = measEnv sp (head bs) cbs tcb lt1s lt2s (f6 ++ bs!!3) (bs!!5) hs info
       γ     <- globalize <$> foldM (+=) γ0 ( [("initEnv", x, y) | (x, y) <- concat (rTrue:tail bs)])
       qcons <- makeQuotDataCons dconM (gsQuotCons $ gsQuots sp)
       ne    <- initNBEEnv (gsQuotTyCons $ gsQuots sp) (gsQuotients $ gsQuots sp) qcons
       return γ {invs = is (invs1 ++ invs2), cgNBEEnv = ne}
  where
    allowTC      = typeclass (getConfig info)
    sp           = giSpec info
    ialias       = mkRTyConIAl (gsIaliases (gsData sp))
    vals f       = map (mapSnd val) . f
    is autoinv   = mkRTyConInv    (gsInvariants (gsData sp) ++ ((Nothing,) <$> autoinv))
    addPolyInfo' = if reflection (getConfig info) then map (mapSnd addPolyInfo) else id

    makeExactDc dcs = if exactDCFlag info then map strengthenDataConType dcs else dcs

addPolyInfo :: SpecType -> SpecType
addPolyInfo t = mkUnivs (go <$> as) ps t'
  where
    (as, ps, t') = bkUniv t
    pos          = tyVarsPosition t'
    go (a,r) = if {- ty_var_value a `elem` ppos pos && -}  ty_var_value a `notElem` pneg pos
               then (setRtvPol a False,r)
               else (a,r)

makeDataConTypes :: Bool -> Var -> CG (Var, SpecType)
makeDataConTypes allowTC x = (x,) <$> trueTy allowTC (varType x)

makeAutoDecrDataCons :: [(Id, SpecType)] -> S.HashSet TyCon -> [Id] -> ([LocSpecType], [(Id, SpecType)])
makeAutoDecrDataCons dcts specenv dcs
  = (simplify rsorts, tys)
  where
    (rsorts, tys) = unzip $ concatMap go tycons
    tycons      = L.nub $ mapMaybe idTyCon dcs

    go tycon
      | S.member tycon specenv =  zipWith (makeSizedDataCons dcts) (tyConDataCons tycon) [0..]
    go _
      = []

    simplify invs = dummyLoc . (`strengthen` invariant) .  fmap (const mempty) <$> L.nub invs
    invariant = MkUReft (F.Reft (F.vv_, F.PAtom F.Ge (lenOf F.vv_) (F.ECon $ F.I 0)) ) mempty

idTyCon :: Id -> Maybe TyCon
idTyCon = fmap dataConTyCon . idDataConM

lenOf :: F.Symbol -> F.Expr
lenOf x = F.mkEApp lenLocSymbol [F.EVar x]

makeSizedDataCons :: [(Id, SpecType)] -> DataCon -> Integer -> (RSort, (Id, SpecType))
makeSizedDataCons dcts x' n = (toRSort $ ty_res trep, (x, fromRTypeRep trep{ty_res = tres}))
    where
      x      = dataConWorkId x'
      st     = fromMaybe (impossible Nothing "makeSizedDataCons: this should never happen") $ L.lookup x dcts
      trep   = toRTypeRep st
      tres   = ty_res trep `strengthen` MkUReft (F.Reft (F.vv_, F.PAtom F.Eq (lenOf F.vv_) computelen)) mempty

      recarguments = filter (\(t,_) -> toRSort t == toRSort tres) (zip (ty_args trep) (ty_binds trep))
      computelen   = foldr (F.EBin F.Plus . lenOf .  snd) (F.ECon $ F.I n) recarguments

mergeDataConTypes ::  F.TCEmb TyCon -> [(Var, SpecType)] -> [(Var, SpecType)] -> [(Var, SpecType)]
mergeDataConTypes tce xts yts = merge (L.sortBy f xts) (L.sortBy f yts)
  where
    f (x,_) (y,_) = compare x y
    merge [] ys = ys
    merge xs [] = xs
    merge (xt@(x, tx):xs) (yt@(y, ty):ys)
      | x == y    = (x, mXY x tx y ty) : merge xs ys
      | x <  y    = xt : merge xs (yt : ys)
      | otherwise = yt : merge (xt : xs) ys
    mXY x tx y ty = meetVarTypes tce (F.pprint x) (getSrcSpan x, tx) (getSrcSpan y, ty)

refreshArgs' :: [(a, SpecType)] -> CG [(a, SpecType)]
refreshArgs' = mapM (mapSndM refreshArgs)


-- | TODO: All this *should* happen inside @Bare@ but appears
--   to happen after certain are signatures are @fresh@-ed,
--   which is why they are here.

-- NV : still some sigs do not get TyConInfo

predsUnify :: TargetSpec -> (Var, RRType RReft) -> (Var, RRType RReft)
predsUnify sp = second (addTyConInfo tce tyi) -- needed to eliminate some @RPropH@
  where
    tce            = gsTcEmbeds (gsName sp)
    tyi            = gsTyconEnv (gsName sp)


--------------------------------------------------------------------------------
measEnv :: TargetSpec
        -> [(F.Symbol, SpecType)]
        -> [CoreBind]
        -> [(F.Symbol, F.Sort)]
        -> [(F.Symbol, F.Sort)]
        -> [(F.Symbol, F.Sort)]
        -> [(F.Symbol, SpecType)]
        -> [(F.Symbol, SpecType)]
        -> [F.Symbol]
        -> TargetInfo
        -> CGEnv
--------------------------------------------------------------------------------
measEnv sp xts cbs _tcb lt1s lt2s asms itys hs info = CGE
  { cgLoc    = Sp.empty
  , renv     = fromListREnv (second val <$> gsMeas (gsData sp)) []
  , syenv    = F.fromListSEnv (gsFreeSyms (gsName sp))
  , litEnv   = F.fromListSEnv lts
  , constEnv = F.fromListSEnv lt2s
  , fenv     = initFEnv $ filterHO (tcb' ++ lts ++ (second (rTypeSort tce . val) <$> gsMeas (gsData sp)))
  , denv     = dmapty val $ gsDicts (gsSig sp)
  , recs     = S.empty
  , invs     = mempty
  , rinvs    = mempty
  , ial      = mkRTyConIAl (gsIaliases (gsData sp))
  , grtys    = fromListREnv xts  []
  , assms    = fromListREnv asms []
  , intys    = fromListREnv itys []
  , emb      = tce
  , tgEnv    = Tg.makeTagEnv cbs
  , tgKey    = Nothing
  , trec     = Nothing
  , lcb      = M.empty
  , forallcb = M.empty
  , holes    = fromListHEnv hs
  , lcs      = mempty
  , cerr     = Nothing
  , cgInfo   = info
  , cgVar    = Nothing
  , cgTopLevel = Nothing
  , cgNBEEnv   = mempty
  }
  where
      tce         = gsTcEmbeds (gsName sp)
      filterHO xs = if higherOrderFlag sp then xs else filter (F.isFirstOrder . snd) xs
      lts         = lt1s ++ lt2s
      tcb'        = []

assm :: TargetInfo -> [(Var, SpecType)]
assm = assmGrty (giImpVars . giSrc)

grty :: TargetInfo -> [(Var, SpecType)]
grty = assmGrty (giDefVars . giSrc)

assmGrty :: (TargetInfo -> [Var]) -> TargetInfo -> [(Var, SpecType)]
assmGrty f info = [ (x, val t) | (x, t) <- sigs, x `S.member` xs ]
  where
    xs          = S.fromList . f             $ info
    sigs        = gsTySigs  . gsSig . giSpec $ info


recSelectorsTy :: TargetInfo -> CG [(Var, SpecType)]
recSelectorsTy info = forM topVs $ \v -> (v,) <$> trueTy (typeclass (getConfig info)) (varType v)
  where
    topVs        = filter isTop $ giDefVars (giSrc info)
    isTop v      = isExportedVar (giSrc info) v && not (v `S.member` sigVs) &&  isRecordSelector v
    sigVs        = S.fromList [v | (v,_) <- gsTySigs sp ++ gsAsmSigs sp ++ gsRefSigs sp ++ gsInSigs sp]
    sp           = gsSig . giSpec $ info



grtyTop :: TargetInfo -> CG [(Var, SpecType)]
grtyTop info     = forM topVs $ \v -> (v,) <$> trueTy (typeclass (getConfig info)) (varType v)
  where
    topVs        = filter isTop $ giDefVars (giSrc info)
    isTop v      = isExportedVar (giSrc info) v && not (v `S.member` sigVs) && not (isRecordSelector v)
    sigVs        = S.fromList [v | (v,_) <- gsTySigs sp ++ gsAsmSigs sp ++ gsRefSigs sp ++ gsInSigs sp]
    sp           = gsSig . giSpec $ info


infoLits :: (TargetSpec -> [(F.Symbol, LocSpecType)]) -> (F.Sort -> Bool) -> TargetInfo -> F.SEnv F.Sort
infoLits litF selF info = F.fromListSEnv $ cbLits ++ measLits
  where
    cbLits    = filter (selF . snd) $ coreBindLits tce info
    measLits  = filter (selF . snd) $ mkSort <$> litF spc
    spc       = giSpec info
    tce       = gsTcEmbeds (gsName spc)
    mkSort    = mapSnd (F.sr_sort . rTypeSortedReft tce . val)

initCGI :: Config -> TargetInfo -> CGInfo
initCGI cfg info = CGInfo {
    fEnv       = F.emptySEnv
  , hsCs       = []
  , hsWfs      = []
  , fixCs      = []
  , fixWfs     = []
  , freshIndex = 0
  , dataConTys = []
  , binds      = F.emptyBindEnv
  , ebinds     = []
  , annotMap   = AI M.empty
  , newTyEnv   = M.fromList (mapSnd val <$> gsNewTypes (gsSig spc))
  , tyConInfo  = tyi
  , tyConEmbed = tce
  , kuts       = mempty
  , kvPacks    = mempty
  , cgLits     = infoLits (gsMeas . gsData) (const True) info
  , cgConsts   = infoLits (gsMeas . gsData) notFn        info
  , cgADTs     = gsADTs nspc
  , termExprs  = M.fromList [(v, es) | (v, _, es) <- gsTexprs (gsSig spc) ]
  , specLVars  = gsLvars (gsVars spc)
  , specLazy   = dictionaryVar `S.insert` gsLazy tspc
  , specTmVars = gsNonStTerm tspc
  , tcheck     = terminationCheck cfg
  , stcheck    = structuralTerm cfg
  , cgiTypeclass = typeclass cfg
  , pruneRefs  = pruneUnsorted cfg
  , logErrors  = []
  , kvProf     = emptyKVProf
  , recCount   = 0
  , bindSpans  = M.empty
  , autoSize   = gsAutosize tspc
  , allowHO    = higherOrderFlag cfg
  , ghcI       = info
  , unsorted   = F.notracepp "UNSORTED" $ F.makeTemplates $ gsUnsorted $ gsData spc
  , nbeState   = mempty
  }
  where
    tce        = gsTcEmbeds nspc
    tspc       = gsTerm spc
    spc        = giSpec info
    tyi        = gsTyconEnv nspc
    nspc       = gsName spc
    notFn      = isNothing . F.functionSort

coreBindLits :: F.TCEmb TyCon -> TargetInfo -> [(F.Symbol, F.Sort)]
coreBindLits tce info
  = sortNub      $ [ (F.symbol x, F.strSort) | (_, Just (F.ESym x)) <- lconsts ]    -- strings
                ++ [ (dconToSym dc, dconToSort dc) | dc <- dcons ]                  -- data constructors
  where
    src         = giSrc info
    lconsts      = literalConst tce <$> literals (giCbs src)
    dcons        = filter isDCon freeVs
    freeVs       = giImpVars src ++ freeSyms
    freeSyms     = fmap snd . gsFreeSyms . gsName . giSpec $ info
    dconToSort   = typeSort tce . expandTypeSynonyms . varType
    dconToSym    = F.symbol . idDataCon
    isDCon x     = isDataConId x && not (hasBaseTypeVar x)

makeQuotDataCons
  :: M.HashMap F.Symbol SpecType
  -> M.HashMap F.Symbol QuotientDataCons
  -> CG (M.HashMap F.Symbol QDataCons)
makeQuotDataCons dcm qdcs = traverse refreshQDataCons $ M.mapMaybeWithKey makeQuotDataCon qdcs
  where
    refreshQDataCons :: QDataCons -> CG QDataCons
    refreshQDataCons dc@QDataCons {..} = do
      quty <- refreshArgs qdcUnderlyingType
      qrts <- traverse refreshArgs qdcRefinedTypes
      return $ dc { qdcUnderlyingType = quty, qdcRefinedTypes = qrts }

    makeQuotDataCon :: F.Symbol -> QuotientDataCons -> Maybe QDataCons
    makeQuotDataCon dc QuotientDataCons {..} = do
      t <- M.lookup dc dcm
      return QDataCons
        { qdcUnderlyingName = qdcBaseTyCon
        , qdcUnderlyingType = t
        , qdcRefinedTypes   = M.fromList $ makeRefined qdcBaseTyCon t <$> qdcQuotTyCons
        }

    makeRefined :: F.Symbol -> SpecType -> (RTyCon, SpecQuotientType, SpecType) -> (F.Symbol, SpecType)
    makeRefined btc t (qtc, QuotientType {..}, utype)
      = case utype of
          RApp (RTyCon c _ _) ts rs _ ->
            let rep@RTypeRep {..} = toRTypeRep t
                mkSub tv u        = (rTyVar tv, u)
                tvs               = Ghc.tyConTyVars c   
                tvsub             = M.fromList $ zipWith mkSub tvs ts
                refine            = doRefine btc qtc qtyTyVars ts rs tvsub
                refineRT (u, r)
                  = (doRefine btc qtc qtyTyVars
                      (map void ts) (map (fmap void) rs) (void <$> tvsub) <$> u, r)
                otvs              = map refineRT $ drop (length tvs) ty_vars   
             in ( F.val qtyName
                , fromRTypeRep rep
                    { ty_vars  = map makeTyVar qtyTyVars ++ otvs
                    , ty_preds = [] -- | TODO: Fix when predicates are added to quotient types
                    , ty_args  = map refine ty_args
                    , ty_res   = refine ty_res
                    }
                )
          _                           -> (F.val qtyName, t)

    doRefine
      :: (F.Reftable r, SubsTy RTyVar RSort r)
      => F.Symbol                    -- | Base type constructor to replace
      -> RTyCon                      -- | Quotient type constructor
      -> [RTyVar]                    -- | Quotient type variables
      -> [RRType r]                  -- | Most general types applied to base type constructor
      -> [RRProp r]                  -- | Most general predicates applied to base type constructor
      -> M.HashMap RTyVar (RRType r) -- | Type variable substitutions to apply
      -> RRType r                    -- | The data constructor type to refine
      -> RRType r
    doRefine _ _ _ _ _ tvs t@(RVar v _)
      | Just u <- M.lookup v tvs = u
      | otherwise                = t
    doRefine btc qtc qtvs ts ps tvs (RFun s inf i o r)
      = RFun s inf (doRefine btc qtc qtvs ts ps tvs i) (doRefine btc qtc qtvs ts ps tvs o) r
    doRefine btc qtc qtvs ts ps tvs (RAllT b t r)
      = RAllT
          (doRefine btc qtc qtvs (void <$> ts) (fmap void <$> ps) (void <$> tvs) <$> b)
          (doRefine btc qtc qtvs ts ps (M.delete (ty_var_value b) tvs) t) r
    doRefine btc qtc qtvs ts ps tvs (RAllP pb t)
      = RAllP
          (doRefine btc qtc qtvs (void <$> ts) (fmap void <$> ps) (void <$> tvs) <$> pb)
          (doRefine btc qtc qtvs ts ps tvs t)
    doRefine btc qtc qtvs ts ps tvs (RApp tc@(RTyCon c _ _) us qs r)
      | F.symbol c == btc, Just qts <- rfargs = RApp qtc qts [] mempty
      | otherwise = RApp tc (map (doRefine btc qtc qtvs ts ps tvs) us) qs r
      where
        mkRType m v       = fromMaybe (RVar v mempty) $ M.lookup v m
        fvs               = M.keysSet tvs
        rfargs            = do
          m <- bifoldMaybe (Unify.simpleUnifyWith fvs) mempty ts us
          return $ map (doRefine btc qtc qtvs ts ps tvs . mkRType m) qtvs
    doRefine btc qtc qtvs ts ps tvs (RApp c us qs r)
      = RApp c (map (doRefine btc qtc qtvs ts ps tvs) us) qs r
    doRefine btc qtc qtvs ts ps tvs (RAllE s a t)
      = RAllE s (doRefine btc qtc qtvs ts ps tvs a) (doRefine btc qtc qtvs ts ps tvs t)
    doRefine btc qtc qtvs ts ps tvs (REx s a t)
      = REx s (doRefine btc qtc qtvs ts ps tvs a) (doRefine btc qtc qtvs ts ps tvs t)
    doRefine btc qtc qtvs ts ps tvs (RAppTy a res r)
      = RAppTy (doRefine btc qtc qtvs ts ps tvs a) (doRefine btc qtc qtvs ts ps tvs res) r
    doRefine btc qtc qtvs ts ps tvs (RRTy e r o t)
      = RRTy (fmap (doRefine btc qtc qtvs ts ps tvs) <$> e) r o (doRefine btc qtc qtvs ts ps tvs t)
    doRefine _ _ _ _ _ _ (RExprArg e) = RExprArg e
    doRefine _ _ _ _ _ _ (RHole r) = RHole r

    makeTyVar :: RTyVar -> (SpecRTVar, RReft)
    makeTyVar tv = (makeRTVar tv, mempty)

    bifoldMaybe :: (a -> b -> c -> Maybe c) -> c -> [a] -> [b] -> Maybe c
    bifoldMaybe _ c []       []       = Just c
    bifoldMaybe f c (a : as) (b : bs) = do
      nc <- f a b c
      bifoldMaybe f nc as bs
    bifoldMaybe _ _ _        _        = Nothing

getQuotientReft :: SpecQuotient -> Maybe F.Expr
getQuotientReft Quotient { qtVars }
  = case mapMaybe getReftExpr (M.toList qtVars) of
      [] -> Nothing
      es -> Just $ F.PAnd es
    where
      getReftExpr :: (F.Symbol, SpecType) -> Maybe F.Expr
      getReftExpr = filterTrivial . substReft . fmap (fmap ur_reft . stripRTypeBase)

      filterTrivial :: Maybe F.Expr -> Maybe F.Expr
      filterTrivial (Just F.PTrue) = Nothing
      filterTrivial e              = e

      substReft :: (F.Symbol, Maybe F.Reft) -> Maybe F.Expr
      substReft (_, Nothing)               = Nothing
      substReft (v, Just (F.Reft (v', e))) = Just $ F.subst1 e (v', F.EVar v)

initNBEEnv
  :: M.HashMap F.Symbol SpecQuotientType
  -> M.HashMap F.Symbol SpecQuotient
  -> M.HashMap F.Symbol QDataCons
  -> CG NBEEnv
initNBEEnv qtcs quots qcons = do
  rs <- gets getReflects
  ss <- gets getSelectors
  dc <- gets getDataCons
  ut <- unfoldTypes rs

  return NBE
    { nbeDefs          = rs
    , nbeSelectors     = ss
    , nbeGuards        = []
    , nbeQuotientTypes = makeQuotTyDef <$> qtcs -- CG.qtdRewrites <$> CG.cgQuotTyDefs γ
    , nbeUnfoldTypes   = ut
    , nbeDataCons
        = NBEDataCons
            { nbeDataConEnv     = dc
            , nbeQuotDataConEnv = qcons
            }
    }
  where
    getReflects :: CGInfo -> M.HashMap F.Symbol NBEDefinition
    getReflects
      = M.fromList
      . map mkNBEDefinition
      . gsHAxioms
      . gsRefl
      . giSpec
      . ghcI

    getSelectors :: CGInfo -> M.HashMap F.Symbol (F.Symbol, Int)
    getSelectors
      = M.fromList
      . concatMap (mapMaybe makeSel . makeSimplify)
      . dataConTys

    getDataCons :: CGInfo -> M.HashMap F.Symbol SpecType
    getDataCons
      = M.fromList
      . map (first F.symbol)
      . dataConTys

    mkNBEDefinition :: (Var, LocSpecType, F.Equation) -> (F.Symbol, NBEDefinition)
    mkNBEDefinition (v, t, F.Equ {..})
      = let s = F.symbol v
         in ( s
            , NBEDefinition
                { nbeType        = F.val t
                , nbeDefinition  = foldr F.ELam eqBody eqArgs
                , nbeIsRecursive = S.member s (F.exprSymbolsSet eqBody)
                }
            )

    makeSel :: F.Rewrite -> Maybe (F.Symbol, (F.Symbol, Int))
    makeSel rw
      | F.EVar x <- F.smBody rw
          = (F.smName rw,) . (F.smDC rw,) <$> L.elemIndex x (F.smArgs rw)
      | otherwise = Nothing

    unfoldTypes :: M.HashMap F.Symbol NBEDefinition -> CG (M.HashMap F.Symbol UnfoldType)
    unfoldTypes ds = do
      isTermCheck <- gets stcheck
      if isTermCheck then
        M.traverseWithKey unfoldType ds
      else
        return mempty

    unfoldType :: F.Symbol -> NBEDefinition -> CG UnfoldType
    unfoldType s NBEDefinition {nbeIsRecursive}
      | nbeIsRecursive = do
          isTermDef <- gets $ doesTerminate s
          return
            $ if isTermDef then
                CompleteUnfold
              else
                LimitedUnfold 1
      | otherwise = return CompleteUnfold

    doesTerminate :: F.Symbol -> CGInfo -> Bool
    doesTerminate s CGInfo {specLVars, specLazy, specTmVars}
      = let s1 = S.map F.symbol specLVars
            s2 = S.map F.symbol specLazy
            s3 = S.map F.symbol specTmVars
         in not (S.member s s1 || S.member s s2 || S.member s s3)

    makeQuotRewrite :: SpecQuotient -> QuotientRewrite
    makeQuotRewrite sq
      = QuotientRewrite
          { rwPattern      = F.val $ qtLeft sq
          , rwExpr         = F.val $ qtRight sq
          , rwFreeVars     = M.keysSet $ qtVars sq
          , rwPrecondition = getQuotientReft sq
          }

    makeQuotTyDef :: SpecQuotientType -> QuotientTypeDef
    makeQuotTyDef sqt
      = QuotientTypeDef
          { qtdName     = qtyName sqt
          , qtdType     = qtyType sqt
          , qtdQuots    = quotients
          , qtdTyVars   = qtyTyVars sqt
          , qtdArity    = qtyArity sqt
          , qtdRewrites = rewrites
          }
        where
          (quotients, rewrites)
            = foldr
                (\q (qs, rws) -> case M.lookup q quots of
                    Nothing -> (qs, rws)
                    Just sq -> (sq : qs, makeQuotRewrite sq : rws)
                ) ([], []) (allQuotients sqt)

          allQuotients QuotientType {qtyType, qtyQuots}
            = case qtyType of
                RApp (QTyCon nm _ _ _ _ _) _ _ _
                  | Just q <- M.lookup (F.val nm) qtcs -> qtyQuots ++ allQuotients q
                _                                         -> qtyQuots
