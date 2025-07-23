{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE OverloadedStrings  #-}

module Language.Haskell.Liquid.Types.QuotDecl
  ( EqualityCtorP  (..)
  , EqualityCtor
  , EqualityCtorParsed
  , EqualityParamP (..)
  , EqualityParam
  , EqualityParamParsed
  , LocTraversable (..)
  , QuotDeclP      (..)
  , QuotDecl
  , QuotDeclLHName
  , QuotDeclParsed
  , QuotDeclR
  , QuotSpecDecl
  , SpecEqualityCtor
  , SpecEqualityParam
  ) where

import           Data.Binary                         (Binary)
import           Data.Generics                       (Data)
import           Data.Hashable                       (Hashable)

import           GHC.Generics                        (Generic, Generically (..))  

import           Language.Fixpoint.Types
  ( ExprV
  , Located
  , LocSymbol
  , SourcePos
  , Symbol
  )
import qualified Language.Fixpoint.Types             as F

import           Language.Haskell.Liquid.Types.Names (LHName)
import           Language.Haskell.Liquid.Types.RType
  ( BareType
  , BareTypeLHName
  , BareTypeParsed
  , BSortV
  , PVarV
  , RRType
  , SizeFunV
  , SpecType
  )
import qualified Language.Haskell.Liquid.GHC.Misc    as Position

import           Text.PrettyPrint.HughesPJ           (Doc, (<+>), ($+$))
import qualified Text.PrettyPrint.HughesPJ           as PPrint
import           Text.Printf                         (printf)

class LocTraversable t where
  traverseWithLoc :: Applicative f => (Located a -> f (Located b)) -> t a -> f (t b)

--------------------------------------------------------------------------------
-- | Equality constructor parameters
--------------------------------------------------------------------------------
type EqualityParam       = EqualityParamP Symbol BareType
type EqualityParamParsed = EqualityParamP LocSymbol BareTypeParsed
type SpecEqualityParam   = EqualityParamP Symbol SpecType
data EqualityParamP v ty
  = EqualityBindParam
      { epBinder :: !Symbol
      , epType   :: Located ty
      }
  | EqualityPrecondition (F.ExprV v)
  deriving (Data, Generic, Eq, Functor, Foldable, Traversable)

instance (Hashable v, Hashable ty) => Hashable (EqualityParamP v ty)
instance (Binary v, Binary ty)     => Binary   (EqualityParamP v ty)

instance (Ord v, F.Fixpoint v, F.PPrint v, F.PPrint ty) => F.PPrint (EqualityParamP v ty) where
  pprintTidy k EqualityBindParam {..}
    = F.pprintTidy k epBinder <> ":" <> F.pprintTidy k epType
  pprintTidy k (EqualityPrecondition e) = "{" <+> F.pprintTidy k e <+> "}"

--------------------------------------------------------------------------------
-- | Equality constructors
--------------------------------------------------------------------------------
type EqualityCtor       = EqualityCtorP Symbol BareType
type EqualityCtorParsed = EqualityCtorP LocSymbol BareTypeParsed
type SpecEqualityCtor   = EqualityCtorP Symbol SpecType
data EqualityCtorP v ty
  = EqualityCtor
      { ecName       :: !(Located Symbol)     -- ^ Equality constructor name
      , ecTyVars     :: [Symbol]              -- ^ Type variable parameters
      , ecTheta      :: [Located ty]          -- ^ Equality constructor theta constraints (e.g. typeclasses)
      , ecParameters :: [EqualityParamP v ty] -- ^ Equality constructor parameters
      , ecLeftTerm   :: ExprV v               -- ^ Left-hand side of the target equality
      , ecRightTerm  :: ExprV v               -- ^ Right-hand side of the target equality
      }
    deriving (Data, Generic, Eq, Functor, Foldable, Traversable)

instance (Hashable v, Hashable ty) => Hashable (EqualityCtorP v ty)
instance (Binary v, Binary ty)     => Binary   (EqualityCtorP v ty)

instance F.Loc (EqualityCtorP v ty) where
  srcSpan = F.srcSpan . ecName

instance (Ord v, F.Fixpoint v, F.PPrint v, F.PPrint ty) => F.PPrint (EqualityCtorP v ty) where
  pprintTidy k EqualityCtor {..}
    =   F.pprintTidy k ecName
    <+> "::"
    <+> ppVars k ecTyVars
    <+> ppThetas k ecTheta
    <+> PPrint.hcat (PPrint.punctuate " ->" $ F.pprintTidy k <$> ecParameters)
    <+> "->"
    <+> F.pprintTidy k ecLeftTerm
    <+> "=="
    <+> F.pprintTidy k ecRightTerm

--------------------------------------------------------------------------------
-- | Quotiented data types
--------------------------------------------------------------------------------
type QuotDecl       = QuotDeclP Symbol BareType
type QuotDeclParsed = QuotDeclP LocSymbol BareTypeParsed
type QuotDeclLHName = QuotDeclP LHName BareTypeLHName
type QuotDeclR r    = QuotDeclP Symbol (RRType r)
type QuotSpecDecl   = QuotDeclP Symbol SpecType
data QuotDeclP v ty
  = QuotDecl
      { qtycName       :: !(Located Symbol) -- ^ Quotient type constructor name
      , qtycTyVars     :: [Symbol]            -- ^ Type variable parameters
      , qtycPVars      :: [PVarV v (BSortV v)]  -- ^ Predicate variable parameters
      , qtycType       :: Located ty          -- ^ Underlying type
      , qtycFirstEqCon :: !(EqualityCtorP v ty) -- ^ The first equality constructor
      , qtycEqCons     :: [EqualityCtorP v ty]  -- ^ The remaining equality constructors
      , qtycSrcPos     :: !SourcePos          -- ^ Source position
      , qtycSFun       :: Maybe (SizeFunV v)    -- ^ Default termination measure
      }
    deriving (Data, Generic, Functor, Foldable, Traversable)
    deriving (Binary, Hashable) via Generically (QuotDeclP v ty)

instance Eq (QuotDeclP v ty) where
  d1 == d2 = qtycName d1 == qtycName d2

instance F.Loc (QuotDeclP v ty) where
  srcSpan = Position.srcSpanFSrcSpan . Position.sourcePosSrcSpan . qtycSrcPos

instance (Ord v, F.Fixpoint v, F.PPrint v, F.PPrint ty) => F.PPrint (QuotDeclP v ty) where
  pprintTidy k QuotDecl {..}
    =   "data"
    <+> F.pprint qtycName
    <+> ppMbSizeFun qtycSFun
    <+> "="
    $+$ PPrint.nest 4
          (PPrint.vcat [ "|/" <+> F.pprintTidy k c | c <- qtycFirstEqCon : qtycEqCons ])

---------------------------------------------
-- Debug printing
---------------------------------------------

instance (Show v, Show ty) => Show (QuotDeclP v ty) where
  show dd = printf "QuotDecl: data = %s, tyvars = %s, sizeFun = %s" -- [at: %s]"
              (show $ qtycName   dd)
              (show $ qtycTyVars dd)
              (show $ qtycSFun   dd)

ppVars :: (F.PPrint a) => F.Tidy -> [a] -> Doc
ppVars k as
  =   "forall"
  <+> PPrint.hcat (PPrint.punctuate " " $ F.pprintTidy k <$> as)
  <+> "."

ppThetas :: F.PPrint a => F.Tidy -> [a] -> Doc
ppThetas _ [] = PPrint.empty
ppThetas k ts
  = PPrint.parens (PPrint.hcat $ PPrint.punctuate ", " $ F.pprintTidy k <$> ts) <+> "=>"

ppMbSizeFun :: F.PPrint v => Maybe (SizeFunV v) -> Doc
ppMbSizeFun Nothing  = ""
ppMbSizeFun (Just z) = F.pprint z

instance LocTraversable (EqualityParamP v) where
  traverseWithLoc f EqualityBindParam {..}
    = EqualityBindParam epBinder <$> f epType
  traverseWithLoc _ (EqualityPrecondition e) = pure $ EqualityPrecondition e

instance LocTraversable (EqualityCtorP v) where
  traverseWithLoc f EqualityCtor {..}
    = let mkEqCon theta params
            = EqualityCtor ecName ecTyVars theta params ecLeftTerm ecRightTerm
       in mkEqCon <$> traverse f ecTheta <*> traverse (traverseWithLoc f) ecParameters

instance LocTraversable (QuotDeclP v) where
  traverseWithLoc f QuotDecl {..}
    = let mkDecl ty eqcon eqcons
            = QuotDecl qtycName qtycTyVars qtycPVars ty eqcon eqcons qtycSrcPos qtycSFun
       in mkDecl
            <$> f qtycType
            <*> traverseWithLoc f qtycFirstEqCon
            <*> traverse (traverseWithLoc f) qtycEqCons
