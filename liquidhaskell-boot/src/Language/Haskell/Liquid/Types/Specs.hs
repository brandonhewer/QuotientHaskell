{-# LANGUAGE DeriveAnyClass #-}
-- | This module contains the top-level structures that hold
--   information about specifications.

{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE StandaloneDeriving         #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Haskell.Liquid.Types.Specs (
  -- * Different types of specifications
  -- $differentSpecTypes
  -- * TargetInfo
  -- $targetInfo
    TargetInfo(..)
  -- * Gathering information about a module
  , TargetSrc(..)
  -- * TargetSpec
  -- $targetSpec
  , TargetSpec(..)
  -- * BareSpec
  -- $bareSpec
  , BareSpec(..)
  -- * LiftedSpec
  -- $liftedSpec
  , LiftedSpec(..)
  -- * Tracking dependencies
  -- $trackingDeps
  , TargetDependencies(..)
  , dropDependency
  -- * Predicates on spec types
  -- $predicates
  , isPLEVar
  , isExportedVar
  -- * Other types
  , QImports(..)
  , Spec(..)
  , GhcSpecVars(..)
  , GhcSpecSig(..)
  , GhcSpecNames(..)
  , GhcSpecTerm(..)
  , GhcSpecRefl(..)
  , GhcSpecData(..)
  , GhcSpecQual(..)
  , BareDef
  , BareMeasure
  , SpecMeasure
  , VarOrLocSymbol
  -- * Legacy data structures
  -- $legacyDataStructures
  , GhcSrc(..)
  , GhcSpec(..)
  -- * Provisional compatibility exports & optics
  -- $provisionalBackCompat
  , toTargetSrc
  , fromTargetSrc
  , toTargetSpec
  , toBareSpec
  , fromBareSpec
  , toLiftedSpec
  , unsafeFromLiftedSpec
  , emptyLiftedSpec
  ) where

import           GHC.Generics            hiding (to, moduleName)
import           Data.Binary
import qualified Language.Fixpoint.Types as F
import           Data.Data (Data)
import           Data.Hashable
import qualified Data.HashSet            as S
import           Data.HashSet            (HashSet)
import qualified Data.HashMap.Strict     as M
import           Data.HashMap.Strict     (HashMap)
import           Language.Haskell.Liquid.Types.DataDecl
import           Language.Haskell.Liquid.Types.Names
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.Variance
import           Language.Haskell.Liquid.Types.Bounds
import           Language.Haskell.Liquid.UX.Config
import           Liquid.GHC.API hiding (Binary, text, (<+>))
import           Language.Haskell.Liquid.GHC.Types
import           Text.PrettyPrint.HughesPJ              (text, (<+>))
import           Text.PrettyPrint.HughesPJ as HughesPJ (($$))


{- $differentSpecTypes

There are different types or \"flavours\" for a specification, depending on its lifecycle. The main goal
is always the same, i.e. refining the Haskell types and produce a final statement (i.e. safe or unsafe)
about the input program. In order to do so, a /specification/ is transformed in the way described by this
picture:

@
    +---------------+                                +-------------------+
    |   BareSpec    |                                |                   |  checked by liquid/liquidOne
    |               |                    ------------|    TargetSpec     |----------------------------- ..
    |(input module) |                   /            |                   |
    +---------------+  makeTargetSpec  /             +-------------------+
           +         -----------------/
    +---------------+                 \\              +-------------------+
    | {LiftedSpec}  |                  \\             |                   |    serialised on disk
    |               |                   -------------|    LiftedSpec     |----------------------------- ..
    |(dependencies) |                                |                   |
    +---------------+                                +-------------------+
          ^                                                    |
          |                   used-as                          |
          +----------------------------------------------------+
@

More specifically, we distinguish:

* 'BareSpec' - is the specification obtained by parsing the Liquid annotations of the input Haskell file.
  It typically contains information about the associated input Haskell module, with the exceptions of
  /assumptions/ that can refer to functions defined in other modules.

* 'LiftedSpec' - is the specification we obtain by \"lifting\" the 'BareSpec'. Most importantly, a
  'LiftedSpec' gets serialised on disk and becomes a /dependency/ for the verification of other 'BareSpec's.

   Lifting in this context consist of:

    1. Perform name-resolution (e.g. make all the relevant GHC's 'Var's qualified, resolve GHC's 'Name's, etc);
    2. Strip the final 'LiftedSpec' with information which are relevant (read: local) to just the input
       'BareSpec'. An example would be /local signatures/, used to annotate internal, auxiliary functions
       within a 'Module';
    3. Strip termination checks, which are /required/ (if specified) for a 'BareSpec' but not for the
       'LiftedSpec'.

* 'TargetSpec' - is the specification we /actually use for refinement/, and is conceptually an
  \"augmented\" 'BareSpec'. You can create a 'TargetSpec' by calling 'makeTargetSpec'.

In order to produce these spec types we have to gather information about the module being compiled by using
the GHC API and retain enough context of the compiled 'Module' in order to be able to construct the types
introduced aboves. The rest of this module introduced also these intermediate structures.
-}

-- $targetInfo
-- The following is the overall type for /specifications/ obtained from
-- parsing the target source and dependent libraries.
-- /IMPORTANT/: A 'TargetInfo' is what is /checked/ by LH itself and it /NEVER/ contains the 'LiftedSpec',
-- because the checking happens only on the 'BareSpec' of the target module.
data TargetInfo = TargetInfo
  { giSrc  :: !TargetSrc
    -- ^ The 'TargetSrc' of the module being checked.
  , giSpec :: !TargetSpec
    -- ^ The 'TargetSpec' of the module being checked.
  }

instance HasConfig TargetInfo where
  getConfig = getConfig . giSpec

-- | The 'TargetSrc' type is a collection of all the things we know about a module being currently
-- checked. It include things like the name of the module, the list of 'CoreBind's,
-- the 'TyCon's declared in this module (that includes 'TyCon's for classes), typeclass instances
-- and so and so forth. It might be consider a sort of 'ModGuts' embellished with LH-specific
-- information (for example, 'giDefVars' are populated with datacons from the module plus the
-- let vars derived from the A-normalisation).
data TargetSrc = TargetSrc
  { giTarget    :: !FilePath              -- ^ Source file for module
  , giTargetMod :: !ModName               -- ^ Name for module
  , giCbs       :: ![CoreBind]            -- ^ Source Code
  , gsTcs       :: ![TyCon]               -- ^ All used Type constructors
  , gsCls       :: !(Maybe [ClsInst])     -- ^ Class instances?
  , giDerVars   :: !(HashSet Var)         -- ^ Binders created by GHC eg dictionaries
  , giImpVars   :: ![Var]                 -- ^ Binders that are _read_ in module (but not defined?)
  , giDefVars   :: ![Var]                 -- ^ (Top-level) binders that are _defined_ in module
  , giUseVars   :: ![Var]                 -- ^ Binders that are _read_ in module
  , gsExports   :: !(HashSet StableName)  -- ^ `Name`s exported by the module being verified
  , gsFiTcs     :: ![TyCon]               -- ^ Family instance TyCons
  , gsFiDcs     :: ![(F.Symbol, DataCon)] -- ^ Family instance DataCons
  , gsPrimTcs   :: ![TyCon]               -- ^ Primitive GHC TyCons (from TysPrim.primTyCons)
  , gsQualImps  :: !QImports              -- ^ Map of qualified imports
  , gsAllImps   :: !(HashSet F.Symbol)    -- ^ Set of _all_ imported modules
  , gsTyThings  :: ![TyThing]             -- ^ All the @TyThing@s known to GHC
  }

-- | 'QImports' is a map of qualified imports.
data QImports = QImports
  { qiModules :: !(S.HashSet F.Symbol)            -- ^ All the modules that are imported qualified
  , qiNames   :: !(M.HashMap F.Symbol [F.Symbol]) -- ^ Map from qualification to full module name
  } deriving Show

-- $targetSpec

-- | A 'TargetSpec' is what we /actually check via LiquidHaskell/. It is created as part of 'mkTargetSpec'
-- alongside the 'LiftedSpec'. It shares a similar structure with a 'BareSpec', but manipulates and
-- transforms the data in preparation to the checking process.
data TargetSpec = TargetSpec
  { gsSig    :: !GhcSpecSig
  , gsQual   :: !GhcSpecQual
  , gsData   :: !GhcSpecData
  , gsName   :: !GhcSpecNames
  , gsVars   :: !GhcSpecVars
  , gsTerm   :: !GhcSpecTerm
  , gsRefl   :: !GhcSpecRefl
  , gsImps   :: ![(F.Symbol, F.Sort)]  -- ^ Imported Environment
  , gsConfig :: !Config
  }
  deriving Show

instance HasConfig TargetSpec where
  getConfig = gsConfig

-- | The collection of GHC 'Var's that a 'TargetSpec' needs to verify (or skip).
data GhcSpecVars = SpVar
  { gsTgtVars    :: ![Var]                        -- ^ Top-level Binders To Verify (empty means ALL binders)
  , gsIgnoreVars :: !(S.HashSet Var)              -- ^ Top-level Binders To NOT Verify (empty means ALL binders)
  , gsLvars      :: !(S.HashSet Var)              -- ^ Variables that should be checked "lazily" in the environment they are used
  , gsCMethods   :: ![Var]                        -- ^ Refined Class methods
  }
  deriving Show

instance Semigroup GhcSpecVars where
  sv1 <> sv2 = SpVar
    { gsTgtVars    = gsTgtVars    sv1 <> gsTgtVars    sv2
    , gsIgnoreVars = gsIgnoreVars sv1 <> gsIgnoreVars sv2
    , gsLvars      = gsLvars      sv1 <> gsLvars      sv2
    , gsCMethods   = gsCMethods   sv1 <> gsCMethods   sv2
    }

instance Monoid GhcSpecVars where
  mempty = SpVar mempty mempty mempty mempty

data GhcSpecQual = SpQual
  { gsQualifiers :: ![F.Qualifier]                -- ^ Qualifiers in Source/Spec files e.g tests/pos/qualTest.hs
  , gsRTAliases  :: ![F.Located SpecRTAlias]      -- ^ Refinement type aliases (only used for qualifiers)
  }
  deriving Show

data GhcSpecSig = SpSig
  { gsTySigs   :: ![(Var, LocSpecType)]           -- ^ Asserted Reftypes
  , gsAsmSigs  :: ![(Var, LocSpecType)]           -- ^ Assumed Reftypes
  , gsAsmReflects  :: ![(Var, Var)]               -- ^ Assumed Reftypes (left is the actual function name and right the pretended one)
  , gsRefSigs  :: ![(Var, LocSpecType)]           -- ^ Reflected Reftypes
  , gsInSigs   :: ![(Var, LocSpecType)]           -- ^ Auto generated Signatures
  , gsNewTypes :: ![(TyCon, LocSpecType)]         -- ^ Mapping of 'newtype' type constructors with their refined types.
  , gsDicts    :: !(DEnv Var LocSpecType)            -- ^ Refined Classes from Instances
  , gsMethods  :: ![(Var, MethodType LocSpecType)]   -- ^ Refined Classes from Classes
  , gsTexprs   :: ![(Var, LocSpecType, [F.Located F.Expr])]  -- ^ Lexicographically ordered expressions for termination
  , gsRelation :: ![(Var, Var, LocSpecType, LocSpecType, RelExpr, RelExpr)]
  , gsAsmRel   :: ![(Var, Var, LocSpecType, LocSpecType, RelExpr, RelExpr)]
  }
  deriving Show

instance Semigroup GhcSpecSig where
  x <> y = SpSig
    { gsTySigs   = gsTySigs x   <> gsTySigs y
    , gsAsmSigs  = gsAsmSigs x  <> gsAsmSigs y
    , gsAsmReflects = gsAsmReflects x <> gsAsmReflects y
    , gsRefSigs  = gsRefSigs x  <> gsRefSigs y
    , gsInSigs   = gsInSigs x   <> gsInSigs y
    , gsNewTypes = gsNewTypes x <> gsNewTypes y
    , gsDicts    = gsDicts x    <> gsDicts y
    , gsMethods  = gsMethods x  <> gsMethods y
    , gsTexprs   = gsTexprs x   <> gsTexprs y
    , gsRelation = gsRelation x <> gsRelation y
    , gsAsmRel   = gsAsmRel x   <> gsAsmRel y
    }







instance Monoid GhcSpecSig where
  mempty = SpSig mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty

data GhcSpecData = SpData
  { gsCtors      :: ![(Var, LocSpecType)]         -- ^ Data Constructor Measure Sigs
  , gsMeas       :: ![(F.Symbol, LocSpecType)]    -- ^ Measure Types eg.  len :: [a] -> Int
  , gsInvariants :: ![(Maybe Var, LocSpecType)]   -- ^ Data type invariants from measure definitions, e.g forall a. {v: [a] | len(v) >= 0}
  , gsIaliases   :: ![(LocSpecType, LocSpecType)] -- ^ Data type invariant aliases
  , gsMeasures   :: ![Measure SpecType DataCon]   -- ^ Measure definitions
  , gsOpaqueRefls:: ![Var]                        -- ^ List of opaque reflected measures
  , gsUnsorted   :: ![UnSortedExpr]
  }
  deriving Show

data GhcSpecNames = SpNames
  { gsFreeSyms   :: ![(F.Symbol, Var)]            -- ^ List of `Symbol` free in spec and corresponding GHC var, eg. (Cons, Cons#7uz) from tests/pos/ex1.hs
  , gsDconsP     :: ![F.Located DataCon]          -- ^ Predicated Data-Constructors, e.g. see tests/pos/Map.hs
  , gsTconsP     :: ![TyConP]                     -- ^ Predicated Type-Constructors, e.g. see tests/pos/Map.hs
  , gsTcEmbeds   :: !(F.TCEmb TyCon)              -- ^ Embedding GHC Tycons into fixpoint sorts e.g. "embed Set as Set_set"
  , gsADTs       :: ![F.DataDecl]                 -- ^ ADTs extracted from Haskell 'data' definitions
  , gsTyconEnv   :: !TyConMap
  }
  deriving Show

deriving instance Show TyConMap

data GhcSpecTerm = SpTerm
  { gsStTerm     :: !(S.HashSet Var)              -- ^ Binders to CHECK by structural termination
  , gsAutosize   :: !(S.HashSet TyCon)            -- ^ Binders to IGNORE during termination checking
  , gsLazy       :: !(S.HashSet Var)              -- ^ Binders to IGNORE during termination checking
  , gsFail       :: !(S.HashSet (F.Located Var))    -- ^ Binders to fail type checking
  , gsNonStTerm  :: !(S.HashSet Var)              -- ^ Binders to CHECK using REFINEMENT-TYPES/termination metrics
  }
  deriving Show

instance Semigroup GhcSpecTerm where
  t1 <> t2 = SpTerm
    { gsStTerm    = gsStTerm t1    <> gsStTerm t2
    , gsAutosize  = gsAutosize t1  <> gsAutosize t2
    , gsLazy      = gsLazy t1      <> gsLazy t2
    , gsFail      = gsFail t1      <> gsFail t2
    , gsNonStTerm = gsNonStTerm t1 <> gsNonStTerm t2
    }

instance Monoid GhcSpecTerm where
  mempty = SpTerm mempty mempty mempty mempty mempty
data GhcSpecRefl = SpRefl
  { gsAutoInst     :: !(S.HashSet Var)                  -- ^ Binders to USE PLE
  , gsHAxioms      :: ![(Var, LocSpecType, F.Equation)] -- ^ Lifted definitions
  , gsImpAxioms    :: ![F.Equation]                     -- ^ Axioms from imported reflected functions
  , gsMyAxioms     :: ![F.Equation]                     -- ^ Axioms from my reflected functions
  , gsReflects     :: ![Var]                            -- ^ Binders for reflected functions
  , gsLogicMap     :: !LogicMap
  , gsWiredReft    :: ![Var]
  , gsRewrites     :: S.HashSet (F.Located Var)
  , gsRewritesWith :: M.HashMap Var [Var]
  }
  deriving Show

instance Semigroup GhcSpecRefl where
  x <> y = SpRefl
    { gsAutoInst = gsAutoInst x <> gsAutoInst y
    , gsHAxioms  = gsHAxioms x <> gsHAxioms y
    , gsImpAxioms = gsImpAxioms x <> gsImpAxioms y
    , gsMyAxioms = gsMyAxioms x <> gsMyAxioms y
    , gsReflects = gsReflects x <> gsReflects y
    , gsLogicMap = gsLogicMap x <> gsLogicMap y
    , gsWiredReft = gsWiredReft x <> gsWiredReft y
    , gsRewrites = gsRewrites x <> gsRewrites y
    , gsRewritesWith = gsRewritesWith x <> gsRewritesWith y
    }

instance Monoid GhcSpecRefl where
  mempty = SpRefl mempty mempty mempty
                  mempty mempty mempty
                  mempty mempty mempty

type VarOrLocSymbol = Either Var LocSymbol
type BareMeasure   = Measure LocBareType F.LocSymbol
type BareDef       = Def     LocBareType F.LocSymbol
type SpecMeasure   = Measure LocSpecType DataCon

-- $bareSpec

-- | A 'BareSpec' is the spec we derive by parsing the Liquid Haskell annotations of a single file. As
-- such, it contains things which are relevant for validation and lifting; it contains things like
-- the pragmas the user defined, the termination condition (if termination-checking is enabled) and so
-- on and so forth. /Crucially/, as a 'BareSpec' is still subject to \"preflight checks\", it may contain
-- duplicates (e.g. duplicate measures, duplicate type declarations etc.) and therefore most of the fields
-- for a 'BareSpec' are lists, so that we can report these errors to the end user: it would be an error
-- to silently ignore the duplication and leave the duplicate resolution to whichever 'Eq' instance is
-- implemented for the relevant field.
--
-- Also, a 'BareSpec' has not yet been subject to name resolution, so it may refer
-- to undefined or out-of-scope entities.
newtype BareSpec =
  MkBareSpec { getBareSpec :: Spec LocBareType F.LocSymbol }
  deriving (Data, Generic, Show, Binary)

instance Semigroup BareSpec where
  x <> y = MkBareSpec { getBareSpec = getBareSpec x <> getBareSpec y }

instance Monoid BareSpec where
  mempty = MkBareSpec { getBareSpec = mempty }


-- instance Semigroup (Spec ty bndr) where

-- | A generic 'Spec' type, polymorphic over the inner choice of type and binder.
data Spec ty bndr  = Spec
  { measures   :: ![Measure ty bndr]                                  -- ^ User-defined properties for ADTs
  , expSigs    :: ![(F.Symbol, F.Sort)]                               -- ^ Exported logic symbols
  , asmSigs    :: ![(F.Located LHName, ty)]                           -- ^ Assumed (unchecked) types; including reflected signatures
  , asmReflectSigs :: ![(F.LocSymbol, F.LocSymbol)]                   -- ^ Assume reflects : left is the actual function and right the pretended one
  , sigs       :: ![(F.Located LHName, ty)]                           -- ^ Asserted spec signatures
  , invariants :: ![(Maybe F.LocSymbol, ty)]                          -- ^ Data type invariants; the Maybe is the generating measure
  , ialiases   :: ![(ty, ty)]                                         -- ^ Data type invariants to be checked
  , dataDecls  :: ![DataDecl]                                         -- ^ Predicated data definitions
  , newtyDecls :: ![DataDecl]                                         -- ^ Predicated new type definitions
  , aliases    :: ![F.Located (RTAlias F.Symbol BareType)]            -- ^ RefType aliases
  , ealiases   :: ![F.Located (RTAlias F.Symbol F.Expr)]              -- ^ Expression aliases
  , embeds     :: !(F.TCEmb (F.Located LHName))                       -- ^ GHC-Tycon-to-fixpoint Tycon map
  , qualifiers :: ![F.Qualifier]                                      -- ^ Qualifiers in source files
  , lvars      :: !(S.HashSet (F.Located LHName))                     -- ^ Variables that should be checked in the environment they are used
  , lazy       :: !(S.HashSet (F.Located LHName))                     -- ^ Ignore Termination Check in these Functions
  , rewrites    :: !(S.HashSet (F.Located LHName))                    -- ^ Theorems turned into rewrite rules
  , rewriteWith :: !(M.HashMap F.LocSymbol [F.LocSymbol])             -- ^ Definitions using rewrite rules
  , fails      :: !(S.HashSet (F.Located LHName))                     -- ^ These Functions should be unsafe
  , reflects   :: !(S.HashSet F.LocSymbol)                            -- ^ Binders to reflect
  , opaqueReflects :: !(S.HashSet F.LocSymbol)                        -- ^ Binders to opaque-reflect
  , autois     :: !(S.HashSet F.LocSymbol)                            -- ^ Automatically instantiate axioms in these Functions
  , hmeas      :: !(S.HashSet F.LocSymbol)                            -- ^ Binders to turn into measures using haskell definitions
  , hbounds    :: !(S.HashSet F.LocSymbol)                            -- ^ Binders to turn into bounds using haskell definitions
  , inlines    :: !(S.HashSet F.LocSymbol)                            -- ^ Binders to turn into logic inline using haskell definitions
  , ignores    :: !(S.HashSet (F.Located LHName))                            -- ^ Binders to ignore during checking; that is DON't check the corebind.
  , autosize   :: !(S.HashSet (F.Located LHName))                     -- ^ Type Constructors that get automatically sizing info
  , pragmas    :: ![F.Located String]                                 -- ^ Command-line configurations passed in through source
  , cmeasures  :: ![Measure ty ()]                                    -- ^ Measures attached to a type-class
  , imeasures  :: ![Measure ty bndr]                                  -- ^ Mappings from (measure,type) -> measure
  , omeasures  :: ![Measure ty bndr]                                  -- ^ Opaque reflection measures.
  -- Separate field bc measures are checked for duplicates, and we want to allow for opaque-reflected measures to be duplicated.
  -- See Note [Duplicate measures and opaque reflection] in "Language.Haskell.Liquid.Measure".
  , classes    :: ![RClass ty]                                        -- ^ Refined Type-Classes
  , relational :: ![(F.Located LHName, F.Located LHName, ty, ty, RelExpr, RelExpr)] -- ^ Relational types
  , asmRel     :: ![(F.Located LHName, F.Located LHName, ty, ty, RelExpr, RelExpr)] -- ^ Assumed relational types
  , termexprs  :: ![(F.Located LHName, [F.Located F.Expr])]                -- ^ Terminating Conditions for functions
  , rinstance  :: ![RInstance ty]
  , dvariance  :: ![(F.Located LHName, [Variance])]                   -- ^ TODO ? Where do these come from ?!
  , dsize      :: ![([ty], F.LocSymbol)]                              -- ^ Size measure to enforce fancy termination
  , bounds     :: !(RRBEnv ty)
  , axeqs      :: ![F.Equation]                                       -- ^ Equalities used for Proof-By-Evaluation
  } deriving (Data, Generic, Show)

instance Binary (Spec LocBareType F.LocSymbol)

instance (Show ty, Show bndr, F.PPrint ty, F.PPrint bndr) => F.PPrint (Spec ty bndr) where
    pprintTidy k sp = text "dataDecls = " <+> pprintTidy k  (dataDecls sp)
                         HughesPJ.$$
                      text "classes = " <+> pprintTidy k (classes sp)
                         HughesPJ.$$
                      text "sigs = " <+> pprintTidy k (sigs sp)

-- /NOTA BENE/: These instances below are considered legacy, because merging two 'Spec's together doesn't
-- really make sense, and we provide this only for legacy purposes.
instance Semigroup (Spec ty bndr) where
  s1 <> s2
    = Spec { measures   =           measures   s1 ++ measures   s2
           , expSigs    =           expSigs    s1 ++ expSigs    s2
           , asmSigs    =           asmSigs    s1 ++ asmSigs    s2
           , asmReflectSigs    =    asmReflectSigs s1 ++ asmReflectSigs s2
           , sigs       =           sigs       s1 ++ sigs       s2
           , invariants =           invariants s1 ++ invariants s2
           , ialiases   =           ialiases   s1 ++ ialiases   s2
           , dataDecls  =           dataDecls  s1 ++ dataDecls  s2
           , newtyDecls =           newtyDecls s1 ++ newtyDecls s2
           , aliases    =           aliases    s1 ++ aliases    s2
           , ealiases   =           ealiases   s1 ++ ealiases   s2
           , qualifiers =           qualifiers s1 ++ qualifiers s2
           , pragmas    =           pragmas    s1 ++ pragmas    s2
           , cmeasures  =           cmeasures  s1 ++ cmeasures  s2
           , imeasures  =           imeasures  s1 ++ imeasures  s2
           , omeasures  =           omeasures  s1 ++ omeasures  s2
           , classes    =           classes    s1 ++ classes    s2
           , relational =           relational s1 ++ relational s2
           , asmRel     =           asmRel     s1 ++ asmRel     s2
           , termexprs  =           termexprs  s1 ++ termexprs  s2
           , rinstance  =           rinstance  s1 ++ rinstance  s2
           , dvariance  =           dvariance  s1 ++ dvariance  s2
           , dsize      =               dsize  s1 ++ dsize      s2
           , axeqs      =           axeqs s1      ++ axeqs s2
           , embeds     = mappend   (embeds   s1)  (embeds   s2)
           , lvars      = S.union   (lvars    s1)  (lvars    s2)
           , lazy       = S.union   (lazy     s1)  (lazy     s2)
           , rewrites   = S.union   (rewrites    s1)  (rewrites    s2)
           , rewriteWith = M.union  (rewriteWith s1)  (rewriteWith s2)
           , fails      = S.union   (fails    s1)  (fails    s2)
           , reflects   = S.union   (reflects s1)  (reflects s2)
           , opaqueReflects   = S.union   (opaqueReflects s1)  (opaqueReflects s2)
           , hmeas      = S.union   (hmeas    s1)  (hmeas    s2)
           , hbounds    = S.union   (hbounds  s1)  (hbounds  s2)
           , inlines    = S.union   (inlines  s1)  (inlines  s2)
           , ignores    = S.union   (ignores  s1)  (ignores  s2)
           , autosize   = S.union   (autosize s1)  (autosize s2)
           , bounds     = M.union   (bounds   s1)  (bounds   s2)
           , autois     = S.union   (autois s1)      (autois s2)
           }

instance Monoid (Spec ty bndr) where
  mappend = (<>)
  mempty
    = Spec { measures   = []
           , expSigs    = []
           , asmSigs    = []
           , asmReflectSigs = []
           , sigs       = []
           , invariants = []
           , ialiases   = []
           , dataDecls  = []
           , newtyDecls = []
           , aliases    = []
           , ealiases   = []
           , embeds     = mempty
           , qualifiers = []
           , lvars      = S.empty
           , lazy       = S.empty
           , rewrites   = S.empty
           , rewriteWith = M.empty
           , fails      = S.empty
           , autois     = S.empty
           , hmeas      = S.empty
           , reflects   = S.empty
           , opaqueReflects = S.empty
           , hbounds    = S.empty
           , inlines    = S.empty
           , ignores    = S.empty
           , autosize   = S.empty
           , pragmas    = []
           , cmeasures  = []
           , imeasures  = []
           , omeasures  = []
           , classes    = []
           , relational = []
           , asmRel     = []
           , termexprs  = []
           , rinstance  = []
           , dvariance  = []
           , dsize      = []
           , axeqs      = []
           , bounds     = M.empty
           }

-- $liftedSpec

-- | A 'LiftedSpec' is derived from an input 'BareSpec' and a set of its dependencies.
-- The general motivations for lifting a spec are (a) name resolution, (b) the fact that some info is
-- only relevant for checking the body of functions but does not need to be exported, e.g.
-- termination measures, or the fact that a type signature was assumed.
-- A 'LiftedSpec' is /what we serialise on disk and what the clients should will be using/.
--
-- What we /do not/ have compared to a 'BareSpec':
--
-- * The 'reflSigs', they are now just \"normal\" signatures;
-- * The 'lazy', we don't do termination checking in lifted specs;
-- * The 'reflects', the reflection has already happened at this point;
-- * The 'hmeas', we have /already/ turned these into measures at this point;
-- * The 'hbounds', ditto as 'hmeas';
-- * The 'inlines', ditto as 'hmeas';
-- * The 'ignores', ditto as 'hmeas';
-- * The 'pragmas', we can't make any use of this information for lifted specs;
-- * The 'termexprs', we don't do termination checking in lifted specs;
--
-- Apart from less fields, a 'LiftedSpec' /replaces all instances of lists with sets/, to enforce
-- duplicate detection and removal on what we serialise on disk.
data LiftedSpec = LiftedSpec
  { liftedMeasures   :: HashSet (Measure LocBareType F.LocSymbol)
    -- ^ User-defined properties for ADTs
  , liftedExpSigs    :: HashSet (F.Symbol, F.Sort)
    -- ^ Exported logic symbols
  , liftedAsmSigs    :: HashSet (F.Located LHName, LocBareType)
    -- ^ Assumed (unchecked) types; including reflected signatures
  , liftedAsmReflectSigs    :: HashSet (F.LocSymbol, F.LocSymbol)
    -- ^ Reflected assumed signatures
  , liftedSigs       :: HashSet (F.Located LHName, LocBareType)
    -- ^ Asserted spec signatures
  , liftedInvariants :: HashSet (Maybe F.LocSymbol, LocBareType)
    -- ^ Data type invariants; the Maybe is the generating measure
  , liftedIaliases   :: HashSet (LocBareType, LocBareType)
    -- ^ Data type invariants to be checked
  , liftedDataDecls  :: HashSet DataDecl
    -- ^ Predicated data definitions
  , liftedNewtyDecls :: HashSet DataDecl
    -- ^ Predicated new type definitions
  , liftedAliases    :: HashSet (F.Located (RTAlias F.Symbol BareType))
    -- ^ RefType aliases
  , liftedEaliases   :: HashSet (F.Located (RTAlias F.Symbol F.Expr))
    -- ^ Expression aliases
  , liftedEmbeds     :: F.TCEmb (F.Located LHName)
    -- ^ GHC-Tycon-to-fixpoint Tycon map
  , liftedQualifiers :: HashSet F.Qualifier
    -- ^ Qualifiers in source/spec files
  , liftedLvars      :: HashSet (F.Located LHName)
    -- ^ Variables that should be checked in the environment they are used
  , liftedAutois     :: S.HashSet F.LocSymbol
    -- ^ Automatically instantiate axioms in these Functions
  , liftedAutosize   :: HashSet (F.Located LHName)
    -- ^ Type Constructors that get automatically sizing info
  , liftedCmeasures  :: HashSet (Measure LocBareType ())
    -- ^ Measures attached to a type-class
  , liftedImeasures  :: HashSet (Measure LocBareType F.LocSymbol)
    -- Lifted opaque reflection measures
  , liftedOmeasures  :: HashSet (Measure LocBareType F.LocSymbol)
    -- ^ Mappings from (measure,type) -> measure
  , liftedClasses    :: HashSet (RClass LocBareType)
    -- ^ Refined Type-Classes
  , liftedRinstance  :: HashSet (RInstance LocBareType)
  , liftedDsize      :: [([LocBareType], F.LocSymbol)]
  , liftedDvariance  :: HashSet (F.Located LHName, [Variance])
    -- ^ ? Where do these come from ?!
  , liftedBounds     :: RRBEnv LocBareType
  , liftedAxeqs      :: HashSet F.Equation
    -- ^ Equalities used for Proof-By-Evaluation
  } deriving (Eq, Data, Generic, Show)
    deriving Hashable via Generically LiftedSpec
    deriving Binary   via Generically LiftedSpec

instance Binary F.Equation

emptyLiftedSpec :: LiftedSpec
emptyLiftedSpec = LiftedSpec
  { liftedMeasures = mempty
  , liftedExpSigs  = mempty
  , liftedAsmSigs  = mempty
  , liftedAsmReflectSigs  = mempty
  , liftedSigs     = mempty
  , liftedInvariants = mempty
  , liftedIaliases   = mempty
  , liftedDataDecls  = mempty
  , liftedNewtyDecls = mempty
  , liftedAliases    = mempty
  , liftedEaliases   = mempty
  , liftedEmbeds     = mempty
  , liftedQualifiers = mempty
  , liftedLvars      = mempty
  , liftedAutois     = mempty
  , liftedAutosize   = mempty
  , liftedCmeasures  = mempty
  , liftedImeasures  = mempty
  , liftedOmeasures  = mempty
  , liftedClasses    = mempty
  , liftedRinstance  = mempty
  , liftedDvariance  = mempty
  , liftedDsize      = mempty
  , liftedBounds     = mempty
  , liftedAxeqs      = mempty
  }

-- $trackingDeps

-- | The /target/ dependencies that concur to the creation of a 'TargetSpec' and a 'LiftedSpec'.
newtype TargetDependencies =
  TargetDependencies { getDependencies :: HashMap StableModule LiftedSpec }
  deriving (Data, Eq, Show, Generic)
  deriving Binary via Generically TargetDependencies

-- instance S.Store TargetDependencies

instance Semigroup TargetDependencies where
  x <> y = TargetDependencies
             { getDependencies = getDependencies x <> getDependencies y
             }


instance Monoid TargetDependencies where
  mempty = TargetDependencies mempty

-- | Drop the given 'StableModule' from the dependencies.
dropDependency :: StableModule -> TargetDependencies -> TargetDependencies
dropDependency sm (TargetDependencies deps) = TargetDependencies (M.delete sm deps)

-- $predicates

-- | Returns 'True' if the input 'Var' is a /PLE/ one.
isPLEVar :: TargetSpec -> Var -> Bool
isPLEVar sp x = S.member x (gsAutoInst (gsRefl sp))

-- | Returns 'True' if the input 'Var' was exported in the module the input 'TargetSrc' represents.
isExportedVar :: TargetSrc -> Var -> Bool
isExportedVar src v = mkStableName n `S.member` ns
  where
    n                = getName v
    ns               = gsExports src

--
-- $legacyDataStructures
--
{-
data GhcInfo = GI
  { _giSrc       :: !GhcSrc
  , _giSpec      :: !GhcSpec               -- ^ All specification information for module
  }
-}

data GhcSrc = Src
  { _giTarget    :: !FilePath              -- ^ Source file for module
  , _giTargetMod :: !ModName               -- ^ Name for module
  , _giCbs       :: ![CoreBind]            -- ^ Source Code
  , _gsTcs       :: ![TyCon]               -- ^ All used Type constructors
  , _gsCls       :: !(Maybe [ClsInst])     -- ^ Class instances?
  , _giDerVars   :: !(S.HashSet Var)       -- ^ Binders created by GHC eg dictionaries
  , _giImpVars   :: ![Var]                 -- ^ Binders that are _read_ in module (but not defined?)
  , _giDefVars   :: ![Var]                 -- ^ (Top-level) binders that are _defined_ in module
  , _giUseVars   :: ![Var]                 -- ^ Binders that are _read_ in module
  , _gsExports   :: !(HashSet StableName)  -- ^ `Name`s exported by the module being verified
  , _gsFiTcs     :: ![TyCon]               -- ^ Family instance TyCons
  , _gsFiDcs     :: ![(F.Symbol, DataCon)] -- ^ Family instance DataCons
  , _gsPrimTcs   :: ![TyCon]               -- ^ Primitive GHC TyCons (from TysPrim.primTyCons)
  , _gsQualImps  :: !QImports              -- ^ Map of qualified imports
  , _gsAllImps   :: !(S.HashSet F.Symbol)  -- ^ Set of _all_ imported modules
  , _gsTyThings  :: ![TyThing]             -- ^ All the @TyThing@s known to GHC
  }

data GhcSpec = SP
  { _gsSig    :: !GhcSpecSig
  , _gsQual   :: !GhcSpecQual
  , _gsData   :: !GhcSpecData
  , _gsName   :: !GhcSpecNames
  , _gsVars   :: !GhcSpecVars
  , _gsTerm   :: !GhcSpecTerm
  , _gsRefl   :: !GhcSpecRefl
  , _gsImps   :: ![(F.Symbol, F.Sort)]  -- ^ Imported Environment
  , _gsConfig :: !Config
  , _gsLSpec  :: !(Spec LocBareType F.LocSymbol) -- ^ Lifted specification for the target module
  }

instance HasConfig GhcSpec where
  getConfig = _gsConfig


toTargetSrc :: GhcSrc -> TargetSrc
toTargetSrc a = TargetSrc
  { giTarget    = _giTarget a
  , giTargetMod = _giTargetMod a
  , giCbs       = _giCbs a
  , gsTcs       = _gsTcs a
  , gsCls       = _gsCls a
  , giDerVars   = _giDerVars a
  , giImpVars   = _giImpVars a
  , giDefVars   = _giDefVars a
  , giUseVars   = _giUseVars a
  , gsExports   = _gsExports a
  , gsFiTcs     = _gsFiTcs a
  , gsFiDcs     = _gsFiDcs a
  , gsPrimTcs   = _gsPrimTcs a
  , gsQualImps  = _gsQualImps a
  , gsAllImps   = _gsAllImps a
  , gsTyThings  = _gsTyThings a
  }

fromTargetSrc :: TargetSrc -> GhcSrc
fromTargetSrc a = Src
  { _giTarget    = giTarget a
  , _giTargetMod = giTargetMod a
  , _giCbs       = giCbs a
  , _gsTcs       = gsTcs a
  , _gsCls       = gsCls a
  , _giDerVars   = giDerVars a
  , _giImpVars   = giImpVars a
  , _giDefVars   = giDefVars a
  , _giUseVars   = giUseVars a
  , _gsExports   = gsExports a
  , _gsFiTcs     = gsFiTcs a
  , _gsFiDcs     = gsFiDcs a
  , _gsPrimTcs   = gsPrimTcs a
  , _gsQualImps  = gsQualImps a
  , _gsAllImps   = gsAllImps a
  , _gsTyThings  = gsTyThings a
  }

toTargetSpec :: GhcSpec -> (TargetSpec, LiftedSpec)
toTargetSpec ghcSpec =
  (targetSpec, (toLiftedSpec . _gsLSpec) ghcSpec)
  where
    targetSpec = TargetSpec
      { gsSig    = _gsSig ghcSpec
      , gsQual   = _gsQual ghcSpec
      , gsData   = _gsData ghcSpec
      , gsName   = _gsName ghcSpec
      , gsVars   = _gsVars ghcSpec
      , gsTerm   = _gsTerm ghcSpec
      , gsRefl   = _gsRefl ghcSpec
      , gsImps   = _gsImps ghcSpec
      , gsConfig = _gsConfig ghcSpec
      }

toBareSpec :: Spec LocBareType F.LocSymbol -> BareSpec
toBareSpec = MkBareSpec

fromBareSpec :: BareSpec -> Spec LocBareType F.LocSymbol
fromBareSpec = getBareSpec

toLiftedSpec :: Spec LocBareType F.LocSymbol -> LiftedSpec
toLiftedSpec a = LiftedSpec
  { liftedMeasures   = S.fromList . measures $ a
  , liftedExpSigs    = S.fromList . expSigs  $ a
  , liftedAsmSigs    = S.fromList . asmSigs  $ a
  , liftedAsmReflectSigs = S.fromList . asmReflectSigs  $ a
  , liftedSigs       = S.fromList . sigs     $ a
  , liftedInvariants = S.fromList . invariants $ a
  , liftedIaliases   = S.fromList . ialiases $ a
  , liftedDataDecls  = S.fromList . dataDecls $ a
  , liftedNewtyDecls = S.fromList . newtyDecls $ a
  , liftedAliases    = S.fromList . aliases $ a
  , liftedEaliases   = S.fromList . ealiases $ a
  , liftedEmbeds     = embeds a
  , liftedQualifiers = S.fromList . qualifiers $ a
  , liftedLvars      = lvars a
  , liftedAutois     = autois a
  , liftedAutosize   = autosize a
  , liftedCmeasures  = S.fromList . cmeasures $ a
  , liftedImeasures  = S.fromList . imeasures $ a
  , liftedOmeasures  = S.fromList . omeasures $ a
  , liftedClasses    = S.fromList . classes $ a
  , liftedRinstance  = S.fromList . rinstance $ a
  , liftedDvariance  = S.fromList . dvariance $ a
  , liftedDsize      = dsize a
  , liftedBounds     = bounds a
  , liftedAxeqs      = S.fromList . axeqs $ a
  }

-- This is a temporary internal function that we use to convert the input dependencies into a format
-- suitable for 'makeGhcSpec'.
unsafeFromLiftedSpec :: LiftedSpec -> Spec LocBareType F.LocSymbol
unsafeFromLiftedSpec a = Spec
  { measures   = S.toList . liftedMeasures $ a
  , expSigs    = S.toList . liftedExpSigs $ a
  , asmSigs    = S.toList . liftedAsmSigs $ a
  , asmReflectSigs = S.toList . liftedAsmReflectSigs $ a
  , sigs       = S.toList . liftedSigs $ a
  , relational = mempty
  , asmRel     = mempty
  , invariants = S.toList . liftedInvariants $ a
  , ialiases   = S.toList . liftedIaliases $ a
  , dataDecls  = S.toList . liftedDataDecls $ a
  , newtyDecls = S.toList . liftedNewtyDecls $ a
  , aliases    = S.toList . liftedAliases $ a
  , ealiases   = S.toList . liftedEaliases $ a
  , embeds     = liftedEmbeds a
  , qualifiers = S.toList . liftedQualifiers $ a
  , lvars      = liftedLvars a
  , lazy       = mempty
  , fails      = mempty
  , rewrites   = mempty
  , rewriteWith = mempty
  , reflects   = mempty
  , opaqueReflects   = mempty
  , autois     = liftedAutois a
  , hmeas      = mempty
  , hbounds    = mempty
  , inlines    = mempty
  , ignores    = mempty
  , autosize   = liftedAutosize a
  , pragmas    = mempty
  , cmeasures  = S.toList . liftedCmeasures $ a
  , imeasures  = S.toList . liftedImeasures $ a
  , omeasures  = S.toList . liftedOmeasures $ a
  , classes    = S.toList . liftedClasses $ a
  , termexprs  = mempty
  , rinstance  = S.toList . liftedRinstance $ a
  , dvariance  = S.toList . liftedDvariance $ a
  , dsize      = liftedDsize  a
  , bounds     = liftedBounds a
  , axeqs      = S.toList . liftedAxeqs $ a
  }
