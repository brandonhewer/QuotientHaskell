{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# OPTIONS_GHC -Wno-x-partial #-}

module Language.Haskell.Liquid.UX.QuasiQuoter
-- (
--     -- * LiquidHaskell Specification QuasiQuoter
--     lq

--     -- * QuasiQuoter Annotations
--   , LiquidQuote(..)
--   ) 
  where

import Data.Data

import qualified Data.Text as T

import Language.Haskell.TH.Lib
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote

import Language.Fixpoint.Types hiding (Error, Loc, SrcSpan, panic)
import qualified Language.Fixpoint.Types as F

import Language.Haskell.Liquid.GHC.Misc (fSrcSpan)
import Liquid.GHC.API  (SrcSpan)
import qualified Liquid.GHC.API as GHC
import qualified GHC.Types.Name.Occurrence
import Language.Haskell.Liquid.Parse
import Language.Haskell.Liquid.Types.Errors
import Language.Haskell.Liquid.Types.Names
import Language.Haskell.Liquid.Types.RType
import Language.Haskell.Liquid.Types.RefType
import Language.Haskell.Liquid.Types.Types

import System.IO
import Text.Megaparsec.Error

--------------------------------------------------------------------------------
-- LiquidHaskell Specification QuasiQuoter -------------------------------------
--------------------------------------------------------------------------------

lq :: QuasiQuoter
lq = QuasiQuoter
  { quoteExp  = bad
  , quotePat  = bad
  , quoteType = bad
  , quoteDec  = lqDec
  }
  where
    -- FIME(adinapoli) Should we preserve 'fail' here?
    bad = error "`lq` quasiquoter can only be used as a top-level declaration"

lqDec :: String -> Q [Dec]
lqDec src = do
  pos <- locSourcePos <$> location
  case singleSpecP pos src of
    Left peb -> do
      runIO (hPutStrLn stderr (errorBundlePretty peb))
      fail "LH quasiquoter parse error"
    Right spec -> do
      prg <- pragAnnD ModuleAnnotation $
               conE 'LiquidQuote `appE` dataToExpQ' spec
      case mkSpecDecs spec of
        Left uerr ->
          throwErrorInQ uerr
        Right decs ->
          return $ prg : decs

throwErrorInQ :: UserError -> Q a
throwErrorInQ uerr =
  fail . showpp =<< runIO (errorsWithContext [uerr])

--------------------------------------------------------------------------------
-- Liquid Haskell to Template Haskell ------------------------------------------
--------------------------------------------------------------------------------

-- Spec to Dec -----------------------------------------------------------------

mkSpecDecs :: BPspec -> Either UserError [Dec]
mkSpecDecs (Asrt (name, ty)) =
  return . SigD (lhNameToName name)
    <$> simplifyBareType name (quantifyFreeRTy $ val ty)
mkSpecDecs (Asrts (names, (ty, _))) =
  (\t -> (`SigD` t) . lhNameToName <$> names)
    <$> simplifyBareType (head names) (quantifyFreeRTy $ val ty)
mkSpecDecs (Alias rta) =
  return . TySynD name tvs <$> simplifyBareType lsym (rtBody (val rta))
  where
    lsym = F.atLoc rta n
    name = symbolName n
    n    = rtName (val rta)
    tvs  = (\a -> PlainTV (symbolName a) BndrReq) <$> rtTArgs (val rta)
mkSpecDecs _ =
  Right []

-- Symbol to TH Name -----------------------------------------------------------

symbolName :: Symbolic s => s -> Name
symbolName = mkName . symbolString . symbol

lhNameToName :: Located LHName -> Name
lhNameToName lname = case val lname of
    LHNUnresolved _ s -> symbolName s
    LHNResolved rn _ -> case rn of
      LHRGHC n -> case GHC.nameModule_maybe n of
        Nothing -> mkName (GHC.getOccString n)
        Just m ->
          mkNameG
            (toTHNameSpace $ GHC.nameNameSpace n)
            (GHC.unitString $ GHC.moduleUnit m)
            (GHC.moduleNameString $ GHC.moduleName m)
            (GHC.getOccString n)
      LHRLocal s -> symbolName s
      LHRIndex i -> panic (Just $ fSrcSpan lname) $ "Cannot produce a TH Name for a LHRIndex " ++ show i
      LHRLogic (LogicName s _m) ->
        panic (Just $ fSrcSpan lname) $ "Cannot produce a TH Name for a LogicName: " ++ show s

  where
    toTHNameSpace :: GHC.NameSpace -> NameSpace
    toTHNameSpace ns
      | ns == GHC.dataName = DataName
      | ns == GHC.tcName = TcClsName
      | ns == GHC.Types.Name.Occurrence.varName = VarName
      | GHC.isFieldNameSpace ns = panic (Just $ fSrcSpan lname) "lhNameToName: Unimplemented case for FieldName NameSpace"
      | otherwise = panic (Just $ fSrcSpan lname) "lhNameToName: Unknown GHC.NameSpace"


-- BareType to TH Type ---------------------------------------------------------

simplifyBareType :: PPrint a => Located a -> BareType -> Either UserError Type
simplifyBareType s t = case simplifyBareType' t of
  Simplified t' ->
    Right t'
  FoundExprArg l ->
    Left $ ErrTySpec l Nothing (pprint $ val s) (pprint t)
      "Found expression argument in bad location in type"
  FoundHole ->
    Left $ ErrTySpec (fSrcSpan s) Nothing (pprint $ val s) (pprint t)
      "Can't write LiquidHaskell type with hole in a quasiquoter"

simplifyBareType' :: BareType -> Simpl Type
simplifyBareType' = simplifyBareType'' ([], [])

simplifyBareType'' :: ([BTyVar], [BareType]) -> BareType -> Simpl Type

simplifyBareType'' ([], []) (RVar v _) =
  return $ VarT $ symbolName v
simplifyBareType'' ([], []) (RAppTy t1 t2 _) =
  AppT <$> simplifyBareType' t1 <*> simplifyBareType' t2
simplifyBareType'' ([], []) (RFun _ _ i o _) =
  (\x y -> ArrowT `AppT` x `AppT` y)
    <$> simplifyBareType' i <*> simplifyBareType' o
simplifyBareType'' ([], []) (RApp cc as _ _) =
  let c' | isFun   cc = ArrowT
         | isTuple cc = TupleT (length as)
         | isList  cc = ListT
         | otherwise = ConT $ lhNameToName (btc_tc cc)
  in  foldl' AppT c' <$> sequenceA (filterExprArgs $ simplifyBareType' <$> as)

simplifyBareType'' _ (RExprArg e) =
  FoundExprArg $ fSrcSpan e
simplifyBareType'' _ (RHole _) =
  FoundHole

simplifyBareType'' s(RAllP _ t) =
  simplifyBareType'' s t
simplifyBareType'' s (RAllE _ _ t) =
  simplifyBareType'' s t
simplifyBareType'' s (REx _ _ t) =
  simplifyBareType'' s t
simplifyBareType'' s (RRTy _ _ _ t) =
  simplifyBareType'' s t

simplifyBareType'' (tvs, cls) (RFun _ _ i o _)
  | isClassType i = simplifyBareType'' (tvs, i : cls) o
simplifyBareType'' (tvs, cls) (RAllT tv t _) =
  simplifyBareType'' (ty_var_value tv : tvs, cls) t

simplifyBareType'' (tvs, cls) bt =
  ForallT ((\t -> PlainTV (symbolName t) SpecifiedSpec) <$> reverse tvs)
    <$> mapM simplifyBareType' (reverse cls)
    <*> simplifyBareType' bt


data Simpl a = Simplified a
             | FoundExprArg SrcSpan
             | FoundHole
               deriving (Functor)

instance Applicative Simpl where
  pure = Simplified

  Simplified   f <*> Simplified   x = Simplified $ f x
  _              <*> FoundExprArg l = FoundExprArg l
  _              <*> FoundHole      = FoundHole
  FoundExprArg l <*> _              = FoundExprArg l
  FoundHole      <*> _              = FoundHole

instance Monad Simpl where
  Simplified   x >>= f = f x
  FoundExprArg l >>= _ = FoundExprArg l
  FoundHole      >>= _ = FoundHole

filterExprArgs :: [Simpl a] -> [Simpl a]
filterExprArgs = filter check
  where
    check (FoundExprArg _) = False
    check _ = True

--------------------------------------------------------------------------------
-- QuasiQuoter Annotations -----------------------------------------------------
--------------------------------------------------------------------------------

newtype LiquidQuote = LiquidQuote { liquidQuoteSpec :: BPspec }
                      deriving (Data, Typeable)

--------------------------------------------------------------------------------
-- Template Haskell Utility Functions ------------------------------------------
--------------------------------------------------------------------------------

locSourcePos :: Loc -> SourcePos
locSourcePos loc =
  uncurry (safeSourcePos (loc_filename loc)) (loc_start loc)

dataToExpQ' :: Data a => a -> Q Exp
dataToExpQ' = dataToExpQ (const Nothing `extQ` textToExpQ)

textToExpQ :: T.Text -> Maybe ExpQ
textToExpQ text = Just $ varE 'T.pack `appE` stringE (T.unpack text)

extQ :: (Typeable a, Typeable b) => (a -> q) -> (b -> q) -> a -> q
extQ f g a = maybe (f a) g (cast a)

