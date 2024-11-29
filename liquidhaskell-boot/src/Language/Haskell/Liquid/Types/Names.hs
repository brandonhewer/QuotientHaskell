{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Haskell.Liquid.Types.Names
  ( lenLocSymbol
  , anyTypeSymbol
  , selfSymbol
  , LogicName (..)
  , LHResolvedName (..)
  , LHName (..)
  , LHNameSpace (..)
  , LHThisModuleNameFlag (..)
  , makeResolvedLHName
  , getLHGHCName
  , getLHNameResolved
  , getLHNameSymbol
  , logicNameToSymbol
  , makeGHCLHName
  , makeGHCLHNameFromId
  , makeGHCLHNameLocated
  , makeGHCLHNameLocatedFromId
  , makeLocalLHName
  , makeLogicLHName
  , makeUnresolvedLHName
  , mapLHNames
  , mapMLocLHNames
  , updateLHNameSymbol
  ) where

import Control.DeepSeq
import qualified Data.Base64.Types                       as Base64
import qualified Data.Binary as B
import qualified Data.ByteString.Lazy                    as ByteString
import qualified Data.ByteString.Base64                  as Base64
import qualified Data.ByteString.Builder                 as Builder
import Data.Data (Data, gmapM, gmapT)
import Data.Generics (extM, extT)
import Data.Hashable
import Data.String (fromString)
import qualified Data.Text                               as Text
import GHC.Generics
import GHC.Stack
import Language.Fixpoint.Types
import Language.Haskell.Liquid.GHC.Misc (locNamedThing) -- Symbolic GHC.Name
import qualified Liquid.GHC.API as GHC
import Text.PrettyPrint.HughesPJ.Compat

-- RJ: Please add docs
lenLocSymbol :: Located Symbol
lenLocSymbol = dummyLoc $ symbol ("autolen" :: String)

anyTypeSymbol :: Symbol
anyTypeSymbol = symbol ("GHC.Prim.Any" :: String)

selfSymbol :: Symbol
selfSymbol = symbol ("liquid_internal_this" :: String)

-- | A name for an entity that does not exist in Haskell
--
-- For instance, this can be used to represent predicate aliases
-- or uninterpreted functions.
data LogicName = LogicName
    { lnSymbol :: !Symbol
      -- | Module where the entity was defined
    , lnModule :: !GHC.Module
      -- | If the named entity is the reflection of some Haskell name
    , lnReflected :: !(Maybe GHC.Name)
    }
  deriving (Data, Eq, Generic)

-- | A name whose procedence is known.
data LHResolvedName
    = LHRLogic !LogicName
    | LHRGHC !GHC.Name    -- ^ A name for an entity that exists in Haskell
    | LHRLocal !Symbol    -- ^ A name for a local variable, e.g. one that is
                          --   bound by a type alias.
    | -- | The index of a name in some environment
      --
      -- Before serializing names, they are converted to indices. The names
      -- themselves are kept in an environment or table that is serialized
      -- separately. This is to acommodate how GHC serializes its Names.
      LHRIndex Word
  deriving (Data, Eq, Generic, Ord)

-- | A name that is potentially unresolved.
data LHName
    = -- | In order to integrate the resolved names gradually, we keep the
      -- unresolved names.
      LHNResolved !LHResolvedName !Symbol
    | LHNUnresolved !LHNameSpace !Symbol
  deriving (Data, Generic)

-- | An Eq instance that ignores the Symbol in resolved names
instance Eq LHName where
  LHNResolved n0 _ == LHNResolved n1 _ = n0 == n1
  LHNUnresolved ns0 s0 == LHNUnresolved ns1 s1 = ns0 == ns1 && s0 == s1
  _ == _ = False

-- | An Ord instance that ignores the Symbol in resolved names
instance Ord LHName where
  compare (LHNResolved n0 _) (LHNResolved n1 _) = compare n0 n1
  compare (LHNUnresolved ns0 s0) (LHNUnresolved ns1 s1) =
    compare (ns0, s0) (ns1, s1)
  compare LHNResolved{} _ = LT
  compare LHNUnresolved{} _ = GT

-- | A Hashable instance that ignores the Symbol in resolved names
instance Hashable LHName where
  hashWithSalt s (LHNResolved n _) = hashWithSalt s n
  hashWithSalt s (LHNUnresolved ns sym) = s `hashWithSalt` ns `hashWithSalt` sym

data LHNameSpace
    = LHTcName
    | LHDataConName LHThisModuleNameFlag
    | LHVarName LHThisModuleNameFlag
  deriving (Data, Eq, Generic, Ord, Show)

instance B.Binary LHNameSpace
instance NFData LHNameSpace
instance Hashable LHNameSpace

-- | Whether the name should be looked up in the current module only or in any
-- module
data LHThisModuleNameFlag = LHThisModuleNameF | LHAnyModuleNameF
  deriving (Data, Eq, Generic, Ord, Show)

instance B.Binary LHThisModuleNameFlag
instance NFData LHThisModuleNameFlag
instance Hashable LHThisModuleNameFlag

instance Ord LogicName where
  compare (LogicName s1 m1 _) (LogicName s2 m2 _) =
    case compare s1 s2 of
      EQ -> GHC.stableModuleCmp m1 m2
      x -> x

instance Show LHName where
  show (LHNResolved _ s) = symbolString s
  show (LHNUnresolved _ s) = symbolString s

instance NFData LHName
instance NFData LHResolvedName
instance NFData LogicName

instance Hashable LHResolvedName where
  hashWithSalt s (LHRLogic n) = s `hashWithSalt` (0::Int) `hashWithSalt` n
  hashWithSalt s (LHRGHC n) =
    s `hashWithSalt` (1::Int) `hashWithSalt` GHC.getKey (GHC.nameUnique n)
  hashWithSalt s (LHRLocal n) = s `hashWithSalt` (2::Int) `hashWithSalt` n
  hashWithSalt s (LHRIndex w) = s `hashWithSalt` (3::Int) `hashWithSalt` w

instance Hashable LogicName where
  hashWithSalt s (LogicName sym m _) =
        s `hashWithSalt` sym
          `hashWithSalt` GHC.moduleStableString m

instance B.Binary LHName
instance B.Binary LHResolvedName where
  get = do
    tag <- B.getWord8
    case tag of
      0 -> LHRLocal . fromString <$> B.get
      1 -> LHRIndex <$> B.get
      _ -> error "B.Binary: invalid tag for LHResolvedName"
  put (LHRLogic _n) = error "cannot serialize LHRLogic"
  put (LHRGHC _n) = error "cannot serialize LHRGHC"
  put (LHRLocal s) = B.putWord8 0 >> B.put (symbolString s)
  put (LHRIndex n) = B.putWord8 1 >> B.put n

instance GHC.Binary LHResolvedName where
  get bh = do
    tag <- GHC.getByte bh
    case tag of
      0 -> LHRLogic <$> GHC.get bh
      1 -> LHRGHC <$> GHC.get bh
      2 -> LHRLocal . fromString <$> GHC.get bh
      _ -> error "GHC.Binary: invalid tag for LHResolvedName"
  put_ bh (LHRLogic n) = GHC.putByte bh 0 >> GHC.put_ bh n
  put_ bh (LHRGHC n) = GHC.putByte bh 1 >> GHC.put_ bh n
  put_ bh (LHRLocal n) = GHC.putByte bh 2 >> GHC.put_ bh (symbolString n)
  put_ _bh (LHRIndex _n) = error "GHC.Binary: cannot serialize LHRIndex"

instance GHC.Binary LogicName where
  get bh = LogicName . fromString <$> GHC.get bh <*> GHC.get bh <*> GHC.get bh
  put_ bh (LogicName s m r) =
    GHC.put_ bh (symbolString s) >> GHC.put_ bh m >> GHC.put_ bh r

instance PPrint LHName where
  pprintTidy _ = text . show

makeResolvedLHName :: LHResolvedName -> Symbol -> LHName
makeResolvedLHName = LHNResolved

makeGHCLHName :: GHC.Name -> Symbol -> LHName
makeGHCLHName n s = makeResolvedLHName (LHRGHC n) s

makeGHCLHNameFromId :: GHC.Id -> LHName
makeGHCLHNameFromId x =
    let n = case GHC.idDetails x of
              GHC.DataConWrapId dc -> GHC.getName dc
              GHC.DataConWorkId dc -> GHC.getName dc
              _ -> GHC.getName x
     in makeGHCLHName n (symbol n)

makeLocalLHName :: Symbol -> LHName
makeLocalLHName s = LHNResolved (LHRLocal s) s

makeLogicLHName :: Symbol -> GHC.Module -> Maybe GHC.Name -> LHName
makeLogicLHName s m r = LHNResolved (LHRLogic (LogicName s m r)) s

makeGHCLHNameLocated :: (GHC.NamedThing a, Symbolic a) => a -> Located LHName
makeGHCLHNameLocated x =
    makeGHCLHName (GHC.getName x) (symbol x) <$ locNamedThing x

makeGHCLHNameLocatedFromId :: GHC.Id -> Located LHName
makeGHCLHNameLocatedFromId x =
    case GHC.idDetails x of
      GHC.DataConWrapId dc -> makeGHCLHNameLocated (GHC.getName dc)
      GHC.DataConWorkId dc -> makeGHCLHNameLocated (GHC.getName dc)
      _ -> makeGHCLHNameLocated x

makeUnresolvedLHName :: LHNameSpace -> Symbol -> LHName
makeUnresolvedLHName = LHNUnresolved

-- | Get the unresolved Symbol from an LHName.
getLHNameSymbol :: LHName -> Symbol
getLHNameSymbol (LHNResolved _ s) = s
getLHNameSymbol (LHNUnresolved _ s) = s

-- | Get the unresolved Symbol from an LHName.
getLHNameResolved :: HasCallStack => LHName -> LHResolvedName
getLHNameResolved (LHNResolved n _) = n
getLHNameResolved n@LHNUnresolved{} = error $ "getLHNameResolved: unresolved name: " ++ show n

getLHGHCName :: LHName -> Maybe GHC.Name
getLHGHCName (LHNResolved (LHRGHC n) _) = Just n
getLHGHCName _ = Nothing

mapLHNames :: Data a => (LHName -> LHName) -> a -> a
mapLHNames f = go
  where
    go :: Data a => a -> a
    go = gmapT (go `extT` f)

mapMLocLHNames :: forall m a. (Data a, Monad m) => (Located LHName -> m (Located LHName)) -> a -> m a
mapMLocLHNames f = go
  where
    go :: forall b. Data b => b -> m b
    go = gmapM (go `extM` f)

updateLHNameSymbol :: (Symbol -> Symbol) -> LHName -> LHName
updateLHNameSymbol f (LHNResolved n s) = LHNResolved n (f s)
updateLHNameSymbol f (LHNUnresolved n s) = LHNUnresolved n (f s)

logicNameToSymbol :: LHName -> Symbol
logicNameToSymbol (LHNResolved (LHRLogic (LogicName s m _)) _) =
    let msymbol = Text.pack $ GHC.moduleNameString $ GHC.moduleName m
        munique =
          Text.dropEnd 2 $ -- Remove padding of two characters "=="
          Base64.extractBase64 $
          Base64.encodeBase64 $
          ByteString.toStrict $
          Builder.toLazyByteString $
          Builder.int32BE $
          fromIntegral $
          hash $
          GHC.unitIdString $
          GHC.moduleUnitId m
     in symbol $ mconcat ["u", munique, "##", msymbol, ".", symbolText s]
logicNameToSymbol (LHNResolved (LHRLocal s) _) = s
logicNameToSymbol n = error $ "logicNameToSymbol: unexpected name: " ++ show n

