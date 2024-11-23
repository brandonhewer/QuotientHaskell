-- | This module provides a GHC 'Plugin' that allows LiquidHaskell to be hooked directly into GHC's
-- compilation pipeline, facilitating its usage and adoption.

{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeApplications           #-}

module Language.Haskell.Liquid.LHNameResolution
  ( resolveLHNames
  , exprArg
  , fromBareSpecLHName
  , toBareSpecLHName
  , LogicNameEnv
  ) where

import           Liquid.GHC.API         as GHC hiding (Expr, panic)
import qualified Language.Haskell.Liquid.GHC.Misc        as LH
import           Language.Haskell.Liquid.Types.Names
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RTypeOp

import           Control.Monad ((<=<), mplus, unless, void)
import           Control.Monad.Identity
import           Control.Monad.State.Strict
import           Data.Bifunctor (first)
import qualified Data.Char                               as Char
import           Data.Coerce (coerce)
import           Data.Data (Data, gmapT)
import           Data.Generics (extT)


import qualified Data.HashSet                            as HS
import qualified Data.HashMap.Strict                     as HM
import           Data.Maybe (fromMaybe, listToMaybe, mapMaybe)
import qualified Data.Text                               as Text
import qualified GHC.Types.Name.Occurrence

import           Language.Fixpoint.Types as F hiding (Error, panic)
import           Language.Haskell.Liquid.Bare.Resolve (lookupLocalVar)
import           Language.Haskell.Liquid.Bare.Types (LocalVars(lvNames), LocalVarDetails(lvdLclEnv))
import qualified Language.Haskell.Liquid.Types.DataDecl as DataDecl
import           Language.Haskell.Liquid.Types.Errors (TError(ErrDupNames, ErrResolve), panic)
import           Language.Haskell.Liquid.Types.Specs as Specs
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.UX.Config
import           Language.Haskell.Liquid.WiredIn

import qualified Text.PrettyPrint.HughesPJ as PJ
import qualified Text.Printf               as Printf

-- | Collects type aliases from the current module and its dependencies.
--
-- It doesn't matter at the moment in which module a type alias is defined.
-- Type alias names cannot be qualified at the moment, and therefore their
-- names identify them uniquely.
collectTypeAliases
  :: Module
  -> BareSpecParsed
  -> TargetDependencies
  -> HM.HashMap Symbol (GHC.Module, RTAlias Symbol ())
collectTypeAliases m spec deps =
    let bsAliases = [ (rtName a, (m, void a)) | a <- map val (aliases spec) ]
        depAliases =
          [ (rtName a, (unStableModule sm, void a))
          | (sm, lspec) <- HM.toList (getDependencies deps)
          , a <- map val (HS.toList $ liftedAliases lspec)
          ]
     in
        HM.fromList $ bsAliases ++ depAliases

-- | Converts occurrences of LHNUnresolved to LHNResolved using the provided
-- type aliases and GlobalRdrEnv.
resolveLHNames
  :: Config
  -> Module
  -> LocalVars
  -> GHC.ImportedMods
  -> GlobalRdrEnv
  -> LogicMap
  -> BareSpecParsed
  -> TargetDependencies
  -> Either [Error] (BareSpec, LogicNameEnv)
resolveLHNames cfg thisModule localVars impMods globalRdrEnv lmap bareSpec0 dependencies =
    let (inScopeEnv, logicNameEnv, unhandledNames) =
          makeInScopeExprEnv impMods thisModule bareSpec0 dependencies
        (bs, (es, ns)) =
          flip runState mempty $ do
            sp1 <- mapMLocLHNames (\l -> (<$ l) <$> resolveLHName l) $
                     fixExpressionArgsOfTypeAliases taliases bareSpec0
            fromBareSpecLHName <$>
              resolveExprNames cfg inScopeEnv globalRdrEnv unhandledNames lmap localVars sp1
        logicNameEnv' =
          foldr (uncurry insertSEnv) logicNameEnv [ (logicNameToSymbol n, n) | n <- ns]
     in if null es then
          Right (bs, logicNameEnv')
        else
          Left es
  where
    taliases = collectTypeAliases thisModule bareSpec0 dependencies

    resolveLHName lname = case val lname of
      LHNUnresolved LHTcName s
        | isTuple s ->
          pure $ LHNResolved (LHRGHC $ GHC.tupleTyConName GHC.BoxedTuple (tupleArity s)) s
        | isList s ->
          pure $ LHNResolved (LHRGHC GHC.listTyConName) s
        | s == "*" ->
          pure $ LHNResolved (LHRGHC GHC.liftedTypeKindTyConName) s
        | otherwise ->
          case HM.lookup s taliases of
            Just (m, _) -> pure $ LHNResolved (LHRLogic $ LogicName s m Nothing) s
            Nothing -> lookupGRELHName LHTcName lname s listToMaybe
      LHNUnresolved ns@(LHVarName lcl) s
        | isDataCon s -> lookupGRELHName (LHDataConName lcl) lname s listToMaybe
        | otherwise ->
            lookupGRELHName ns lname s
              (fmap (either id GHC.getName) . lookupLocalVar localVars (atLoc lname s))
      LHNUnresolved ns s -> lookupGRELHName ns lname s listToMaybe
      n@(LHNResolved (LHRLocal _) _) -> pure n
      n ->
        let sp = Just $ LH.sourcePosSrcSpan $ loc lname
         in panic sp $ "resolveLHNames: Unexpected resolved name: " ++ show n

    lookupGRELHName ns lname s localNameLookup =
      case maybeDropImported ns $ GHC.lookupGRE globalRdrEnv (mkLookupGRE ns s) of
        [e] -> do
          let n = GHC.greName e
              n' = fromMaybe n $ localNameLookup [n]
          pure $ LHNResolved (LHRGHC n') s
        es@(_:_) -> do
          let topLevelNames = map GHC.greName es
          case localNameLookup topLevelNames of
            Just n | notElem n topLevelNames ->
              pure $ LHNResolved (LHRGHC n) s
            _ -> do
              addError
                (ErrDupNames
                   (LH.fSrcSpan lname)
                   (pprint s)
                   (map (PJ.text . showPprUnsafe) es)
                )
              pure $ val lname
        [] ->
          case localNameLookup [] of
            Just n' ->
              pure $ LHNResolved (LHRGHC n') s
            Nothing -> do
              addError
                (errResolve (nameSpaceKind ns) "Cannot resolve name" (s <$ lname))
              pure $ val lname

    errResolve :: PJ.Doc -> String -> LocSymbol -> Error
    errResolve k msg lx = ErrResolve (LH.fSrcSpan lx) k (pprint (val lx)) (PJ.text msg)

    maybeDropImported ns es
      | localNameSpace ns = filter GHC.isLocalGRE es
      | otherwise = es

    localNameSpace = \case
      LHDataConName lcl -> lcl == LHThisModuleNameF
      LHVarName lcl -> lcl == LHThisModuleNameF
      LHTcName -> False

    nameSpaceKind :: LHNameSpace -> PJ.Doc
    nameSpaceKind = \case
      LHTcName -> "type constructor"
      LHDataConName LHAnyModuleNameF -> "data constructor"
      LHDataConName LHThisModuleNameF -> "locally-defined data constructor"
      LHVarName LHAnyModuleNameF -> "variable"
      LHVarName LHThisModuleNameF -> "variable from the current module"

    tupleArity s =
      let a = read $ drop 5 $ symbolString s
       in if a > 64 then
            error $ "tupleArity: Too large (more than 64): " ++ show a
          else
            a

    isDataCon s = case Text.uncons (Text.takeWhileEnd (/= '.') (symbolText s)) of
      Just (c, _) -> Char.isUpper c || c == ':'
      Nothing -> False

type RenameOutput = ([Error], [LHName])

addError :: Error -> State RenameOutput ()
addError e = modify (first (e :))

addName :: LHName -> State RenameOutput ()
addName n = modify (fmap (n:))

mkLookupGRE :: LHNameSpace -> Symbol -> LookupGRE GHC.GREInfo
mkLookupGRE ns s =
    let m = LH.takeModuleNames s
        n = LH.dropModuleNames s
        nString = symbolString n
        oname = GHC.mkOccName (mkGHCNameSpace ns) nString
        rdrn =
          if m == "" then
            GHC.mkRdrUnqual oname
          else
            GHC.mkRdrQual (GHC.mkModuleName $ symbolString m) oname
     in GHC.LookupRdrName rdrn (mkWhichGREs ns)
  where
    mkWhichGREs :: LHNameSpace -> WhichGREs GHC.GREInfo
    mkWhichGREs = \case
      LHTcName -> GHC.SameNameSpace
      LHDataConName _ -> GHC.SameNameSpace
      LHVarName _ -> GHC.RelevantGREs
        { GHC.includeFieldSelectors = GHC.WantNormal
        , GHC.lookupVariablesForFields = True
        , GHC.lookupTyConsAsWell = False
        }

    mkGHCNameSpace = \case
      LHTcName -> GHC.tcName
      LHDataConName _ -> GHC.dataName
      LHVarName _ -> GHC.Types.Name.Occurrence.varName

-- | Changes unresolved names to local resolved names in the body of type
-- aliases.
resolveBoundVarsInTypeAliases :: BareSpecParsed -> BareSpecParsed
resolveBoundVarsInTypeAliases = updateAliases resolveBoundVars
  where
    resolveBoundVars boundVars = \case
      LHNUnresolved LHTcName s ->
        if elem s boundVars then
          LHNResolved (LHRLocal s) s
        else
          LHNUnresolved LHTcName s
      n ->
        error $ "resolveLHNames: Unexpected resolved name: " ++ show n

    -- Applies a function to the body of type aliases, passes to every call the
    -- arguments of the alias.
    updateAliases f spec =
       spec
            { aliases = [ Loc sp0 sp1 (a { rtBody = mapLHNames (f args) (rtBody a) })
                        | Loc sp0 sp1 a <- aliases spec
                        , let args = rtTArgs a ++ rtVArgs a
                        ]
            }

-- | The expression arguments of type aliases are initially parsed as
-- types. This function converts them to expressions.
--
-- For instance, in @Prop (Ev (plus n n))@ where `Prop` is the alias
--
-- > {-@ type Prop E = {v:_ | prop v = E} @-}
--
-- the parser builds a type for @Ev (plus n n)@.
--
fixExpressionArgsOfTypeAliases
  :: HM.HashMap Symbol (Module, RTAlias Symbol ())
  -> BareSpecParsed
  -> BareSpecParsed
fixExpressionArgsOfTypeAliases taliases =
    mapBareTypes go . resolveBoundVarsInTypeAliases
  where
    go :: BareTypeParsed -> BareTypeParsed
    go (RApp c@(BTyCon { btc_tc = Loc _ _ (LHNUnresolved LHTcName s) }) ts rs r)
      | Just (_, rta) <- HM.lookup s taliases =
        RApp c (fixExprArgs (btc_tc c) rta (map go ts)) (map goRef rs) r
    go (RApp c ts rs r) =
        RApp c (map go ts) (map goRef rs) r
    go (RAppTy t1 t2 r)  = RAppTy (go t1) (go t2) r
    go (RFun  x i t1 t2 r) = RFun  x i (go t1) (go t2) r
    go (RAllT a t r)     = RAllT a (go t) r
    go (RAllP a t)       = RAllP a (go t)
    go (RAllE x t1 t2)   = RAllE x (go t1) (go t2)
    go (REx x t1 t2)     = REx   x (go t1) (go t2)
    go (RRTy e r o t)    = RRTy  e r o     (go t)
    go t@RHole{}         = t
    go t@RVar{}          = t
    go t@RExprArg{}      = t
    goRef (RProp ss t)   = RProp ss (go t)

    fixExprArgs lname rta ts =
      let n = length (rtTArgs rta)
          (targs, eargs) = splitAt n ts
          msg = "FIX-EXPRESSION-ARG: " ++ showpp (rtName rta)
          toExprArg = exprArg (LH.fSourcePos lname) msg
       in targs ++ [ RExprArg $ toExprArg e <$ lname | e <- eargs ]

mapBareTypes :: (BareTypeParsed -> BareTypeParsed) -> BareSpecParsed -> BareSpecParsed
mapBareTypes f  = go
  where
    go :: Data a => a -> a
    go = gmapT (go `extT` f)

-- | exprArg converts a tyVar to an exprVar because parser cannot tell
--   this function allows us to treating (parsed) "types" as "value"
--   arguments, e.g. type Matrix a Row Col = List (List a Row) Col
--   Note that during parsing, we don't necessarily know whether a
--   string is a type or a value expression. E.g. in tests/pos/T1189.hs,
--   the string `Prop (Ev (plus n n))` where `Prop` is the alias:
--     {-@ type Prop E = {v:_ | prop v = E} @-}
--   the parser will chomp in `Ev (plus n n)` as a `BareType` and so
--   `exprArg` converts that `BareType` into an `Expr`.
exprArg :: SourcePos -> String -> BareTypeParsed -> ExprV LocSymbol
exprArg l msg = notracepp ("exprArg: " ++ msg) . go
  where
    go :: BareTypeParsed -> ExprV LocSymbol
    go (RExprArg e)     = val e
    go (RVar (BTV x) _)       = EVar x
    go (RApp x [] [] _) = EVar (getLHNameSymbol <$> btc_tc x)
    go (RApp f ts [] _) = eApps (EVar (getLHNameSymbol <$> btc_tc f)) (go <$> ts)
    go (RAppTy t1 t2 _) = EApp (go t1) (go t2)
    go z                = panic sp $ Printf.printf "Unexpected expression parameter: %s in %s" (show $ parsedToBareType z) msg
    sp                  = Just (LH.sourcePosSrcSpan l)

-- | An environment of names in scope
--
-- For each symbol we have the aliases with which it is imported and the
-- name corresponding to each alias.
type InScopeExprEnv = SEnv [(GHC.ModuleName, LHName)]

-- | Looks the names in scope with the given symbol.
-- Returns a list of close but different symbols or a non empty list
-- with the matched names.
lookupInScopeExprEnv :: InScopeExprEnv -> Symbol -> Either [Symbol] [LHName]
lookupInScopeExprEnv env s = do
    let n = LH.dropModuleNames s
    case lookupSEnvWithDistance n env of
      Alts closeSyms -> Left closeSyms
      F.Found xs -> do
         let q = LH.takeModuleNames s
         case filter ((mkFastString (symbolString q) ==) . GHC.moduleNameFS . fst) xs of
           [] -> Left $ map ((`LH.qualifySymbol` n) . symbol . GHC.moduleNameString . fst) xs
           ys -> Right $ map snd ys

-- | For every symbol tells the corresponding LHName
--
-- Symbols are expected to follow a precise syntax
--
-- > <package unique> ## module name ## name
--
-- as created by 'logicNameToSymbol'.
--
type LogicNameEnv = SEnv LHName

-- | Builds an 'InScopeExprEnv' from the module aliases for the current module,
-- the spec of the current module, and the specs of the dependencies.
--
-- Also returns a LogicNameEnv constructed from the same names.
-- Also returns the set of all names that aren't handled yet by name resolution.
makeInScopeExprEnv
  :: GHC.ImportedMods
  -> GHC.Module
  -> BareSpecParsed
  -> TargetDependencies
  -> ( InScopeExprEnv
     , LogicNameEnv
     , HS.HashSet Symbol
     )
makeInScopeExprEnv impAvails thisModule spec dependencies =
    let unqualify s =
          if s == LH.qualifySymbol (symbol $ GHC.moduleName thisModule) (LH.dropModuleNames s) then
            LH.dropModuleNames s
          else
            s
        -- Names should be removed from this list as they are supported
        -- by renaming.
        unhandledNames = HS.fromList $
          map unqualify unhandledNamesList ++ map (LH.qualifySymbol (symbol $ GHC.moduleName thisModule)) unhandledNamesList
        unhandledNamesList = concat $
          [ map (getLHNameSymbol . val) $ HS.toList $ reflects spec
          , map (getLHNameSymbol . val) $ HS.toList $ opaqueReflects spec
          , map (getLHNameSymbol . val) $ HS.toList $ hmeas spec
          , map (getLHNameSymbol . val) $ HS.toList $ inlines spec
          , map (getLHNameSymbol . val . fst) $ asmReflectSigs spec
          , map (val . msName) $ measures spec
          , map (val . msName) $ cmeasures spec
          , map (rtName . val) $ ealiases spec
          , map fst $
             concatMap (DataDecl.dcpTyArgs . val) wiredDataCons
          , map fst $
             concatMap DataDecl.dcFields $ concat $
             mapMaybe DataDecl.tycDCons $
             dataDecls spec
          , map fst wiredSortedSyms
          ] ++ map (map getLHNameSymbol . snd) logicNames
        logicNames =
          (thisModule, []) :
          [ (unStableModule sm, collectLiftedSpecLogicNames sp)
          | (sm, sp) <- HM.toList $ getDependencies dependencies
          ]
     in
        ( unionAliasEnvs $ map mkAliasEnv logicNames
        , mkLogicNameEnv $ concatMap snd logicNames
        , unhandledNames
        )
  where
    mkAliasEnv (m, lhnames) =
      let aliases = moduleAliases m
       in fromListSEnv
            [ (s,  map (,lhname) aliases)
            | lhname@(LHNResolved (LHRLogic (LogicName s _ _))_) <- lhnames
            ]

    unionAliasEnvs :: [InScopeExprEnv] -> InScopeExprEnv
    unionAliasEnvs = coerce . foldl' (HM.unionWith (++)) HM.empty . coerce @[InScopeExprEnv] @[HM.HashMap Symbol [(GHC.ModuleName, LHName)]]

    moduleAliases m =
      case GHC.lookupModuleEnv impAvails m of
        Just impBys -> concatMap imvAliases $ GHC.importedByUser impBys
        Nothing -> [GHC.moduleName m, GHC.mkModuleName ""]

    imvAliases imv
      | GHC.imv_qualified imv = [GHC.imv_name imv]
      | otherwise = [GHC.imv_name imv, GHC.mkModuleName ""]

    mkLogicNameEnv names = fromListSEnv [ (logicNameToSymbol n, n) | n <- names ]

collectLiftedSpecLogicNames :: LiftedSpec -> [LHName]
collectLiftedSpecLogicNames sp =
    concat
      [ map (makeLocalLHName . LH.dropModuleNames . getLHNameSymbol . fst) $ HS.toList $ liftedExpSigs sp
      , map (makeLocalLHName . LH.dropModuleNames . val . msName) $ HS.toList $ liftedCmeasures sp
      , map (makeLocalLHName . LH.dropModuleNames . val . msName) $ HS.toList $ liftedMeasures sp
      , map (makeLocalLHName . LH.dropModuleNames . rtName . val) $ HS.toList $ liftedEaliases sp
      , map (makeLocalLHName . LH.dropModuleNames . fst) $
        concatMap DataDecl.dcFields $ concat $
        mapMaybe DataDecl.tycDCons $
        HS.toList $ liftedDataDecls sp
      , map (makeLocalLHName . LH.dropModuleNames . eqName) $ HS.toList $ liftedAxeqs sp
      ]

resolveExprNames
  :: Config
  -> InScopeExprEnv
  -> GHC.GlobalRdrEnv
  -> HS.HashSet Symbol
  -> LogicMap
  -> LocalVars
  -> BareSpecParsed
  -> State RenameOutput BareSpecLHName
resolveExprNames cfg env globalRdrEnv unhandledNames lmap localVars sp =
    emapSpecM
      (bscope cfg)
      (map localVarToSymbol . maybe [] lvdLclEnv . (GHC.lookupNameEnv (lvNames localVars) <=< getLHGHCName))
      resolveName
      (\ss0 ->
        emapReftM (bscope cfg)
          resolveName
          (\ss1 ->
            emapUReftVM
              (resolveName . (ss1 ++))
              (emapFReftM (resolveName . (ss1 ++)))
          )
          ss0
      )
      sp
  where
    localVarToSymbol = F.symbol . GHC.occNameString . GHC.nameOccName . GHC.varName

    resolveName :: [Symbol] -> LocSymbol -> State RenameOutput LHName
    resolveName ss ls
      | elem s ss = return $ makeLocalLHName s
      | otherwise =
        case lookupInScopeExprEnv env s of
          Left alts ->
            case resolveDataConName ls `mplus` resolveVarName ls of
              Just m -> m
              Nothing -> do
                unless (HS.member s unhandledNames) $
                  addError (errResolveLogicName ls alts)
                return $ makeLocalLHName s
          Right [lhname] ->
            return lhname
          Right names -> do
            addError (ErrDupNames (LH.fSrcSpan ls) (pprint s) (map pprint names))
            return $ makeLocalLHName s
      where
        s = val ls

    errResolveLogicName s alts =
      ErrResolve
        (LH.fSrcSpan s)
        (PJ.text "logic name")
        (pprint $ val s)
        (if null alts then
           PJ.text "Cannot resolve name"
         else
           PJ.text "Cannot resolve name" PJ.$$
           PJ.sep (PJ.text "Maybe you meant one of:" : map pprint alts)
        )

    resolveDataConName ls
      | LH.dropModuleNames s == ":" = Just $
        return $ makeLocalLHName s
      | LH.dropModuleNames s == "[]" = Just $
        return $ makeLocalLHName s
      | isTupleDC (symbolText s) = Just $
        return $ makeLocalLHName s
        -- TODO: Remove this case when qualified names are handled
      | LH.takeModuleNames s /= "" = Just $
        return $ makeLocalLHName s
      where
        s = val ls
        isTupleDC t =
          Text.isPrefixOf "(" t && Text.isSuffixOf ")" t &&
          Text.all (== ',') (Text.init $ Text.tail t)
    resolveDataConName s =
      case GHC.lookupGRE globalRdrEnv (mkLookupGRE (LHDataConName LHAnyModuleNameF) $ val s) of
        [e] -> do
          let n = GHC.greName e
          Just $ do
            let lhName = makeLogicLHName (symbol n) (GHC.nameModule n)  (Just n)
            addName lhName
            -- return lhName
            return $ makeLocalLHName $ val s
        [] ->
          Nothing
        es ->
          Just $ do
            addError
              (ErrDupNames
                 (LH.fSrcSpan s)
                 (pprint $ val s)
                 (map (PJ.text . showPprUnsafe) es)
              )
            return $ makeLocalLHName $ val s

    resolveVarName s
      | val s == "GHC.Internal.Base.." = Just $ do
        return $ makeLocalLHName $ val s
    resolveVarName s =
      case GHC.lookupGRE globalRdrEnv (mkLookupGRE (LHVarName LHAnyModuleNameF) (val s)) of
        [e] -> do
          let n = GHC.greName e
          if HM.member (symbol n) (lmSymDefs lmap) then
            Just $ do
              let lhName = makeLogicLHName (symbol n) (GHC.nameModule n) (Just n)
              addName lhName
              -- return lhName
              return $ makeLocalLHName $ val s
          else
            Nothing
        [] ->
          Nothing
        es ->
          Just $ do
            addError
              (ErrDupNames
                 (LH.fSrcSpan s)
                 (pprint $ val s)
                 (map (PJ.text . showPprUnsafe) es)
              )
            return $ makeLocalLHName $ val s

toBareSpecLHName :: Config -> LogicNameEnv -> BareSpec -> BareSpecLHName
toBareSpecLHName cfg env sp0 = runIdentity $ go sp0
  where
    -- This is implemented with a monadic traversal to reuse the logic
    -- that collects the local symbols in scope.
    go :: BareSpec -> Identity BareSpecLHName
    go sp =
      emapSpecM
        (bscope cfg)
        (const [])
        resolveName
        (\ss0 ->
          emapReftM (bscope cfg)
            resolveName
            (\ss1 ->
              emapUReftVM
                (resolveName . (ss1 ++))
                (emapFReftM (resolveName . (ss1 ++)))
            )
            ss0
        )
        sp

    unhandledNames = HS.fromList $ map fst $ expSigs sp0

    resolveName :: [Symbol] -> Symbol -> Identity LHName
    resolveName ss s
      | elem s ss = return $ makeLocalLHName s
      | otherwise =
        case lookupSEnv s env of
          Nothing -> do
            unless (HS.member s unhandledNames) $
              panic Nothing $ "toBareSpecLHName: cannot find " ++ show s
            return $ makeLocalLHName s
          Just lhname -> return lhname
