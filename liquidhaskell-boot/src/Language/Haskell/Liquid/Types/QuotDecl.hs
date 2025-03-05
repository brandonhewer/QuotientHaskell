{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE OverloadedStrings  #-}

module Language.Haskell.Liquid.Types.QuotDecl
  ( EqualityCtorP (..)
  , EqualityCtor
  , EqualityCtorParsed
  , EqualityParamP (..)
  , EqualityParam
  , EqualityParamParsed
  , QuotDeclP (..)
  , QuotDecl
  , QuotDeclParsed
  , QuotDeclLHName
  ) where

import           Data.Binary                         (Binary)
import           Data.Generics                       (Data)
import           Data.Hashable                       (Hashable)
import           Data.Typeable                       (Typeable)

import           GHC.Generics                        (Generic, Generically (..))  

import qualified Language.Fixpoint.Types             as F

import           Language.Haskell.Liquid.Types.Names (LHName)
import           Language.Haskell.Liquid.Types.RType
  ( BareType
  , BareTypeLHName
  , BareTypeParsed
  , BSortV
  , PVarV
  , SizeFunV
  )
import qualified Language.Haskell.Liquid.GHC.Misc    as Position

import           Text.PrettyPrint.HughesPJ           (Doc, (<+>), ($+$))
import qualified Text.PrettyPrint.HughesPJ           as PPrint
import           Text.Printf                         (printf)

--------------------------------------------------------------------------------
-- | Equality constructor parameters
--------------------------------------------------------------------------------
type EqualityParam       = EqualityParamP F.Symbol BareType
type EqualityParamParsed = EqualityParamP F.LocSymbol BareTypeParsed
data EqualityParamP v ty
  = EqualityBindParam
      { epBinder :: !F.Symbol
      , epType   :: ty
      }
  | EqualityPrecondition (F.ExprV v)
  deriving (Data, Typeable, Generic, Eq, Functor, Foldable, Traversable)

instance (Hashable v, Hashable ty) => Hashable (EqualityParamP v ty)
instance (Binary v, Binary ty)     => Binary   (EqualityParamP v ty)

instance (Ord v, F.Fixpoint v, F.PPrint v, F.PPrint ty) => F.PPrint (EqualityParamP v ty) where
  pprintTidy k EqualityBindParam {..}
    = F.pprintTidy k epBinder <> ":" <> F.pprintTidy k epType
  pprintTidy k (EqualityPrecondition e) = "{" <+> F.pprintTidy k e <+> "}"

--------------------------------------------------------------------------------
-- | Equality constructors
--------------------------------------------------------------------------------
type EqualityCtor       = EqualityCtorP F.Symbol BareType
type EqualityCtorParsed = EqualityCtorP F.LocSymbol BareTypeParsed
data EqualityCtorP v ty
  = EqualityCtor
      { ecName       :: !(F.Located F.Symbol) -- ^ Equality constructor name
      , ecTyVars     :: [F.Symbol]            -- ^ Type variable parameters
      , ecTheta      :: [F.Located ty]        -- ^ Equality constructor theta constraints (e.g. typeclasses)
      , ecParameters :: [EqualityParamP v ty] -- ^ Equality constructor parameters
      , ecLeftTerm   :: F.ExprV v             -- ^ Left-hand side of the target equality
      , ecRightTerm  :: F.ExprV v             -- ^ Right-hand side of the target equality
      }
    deriving (Data, Typeable, Generic, Eq, Functor, Foldable, Traversable)

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
type QuotDecl       = QuotDeclP F.Symbol BareType
type QuotDeclParsed = QuotDeclP F.LocSymbol BareTypeParsed
type QuotDeclLHName = QuotDeclP LHName BareTypeLHName
data QuotDeclP v ty
  = QuotDecl
      { qtycName       :: !(F.Located LHName)   -- ^ Quotient type constructor name
      , qtycTyVars     :: [F.Symbol]            -- ^ Type variable parameters
      , qtycPVars      :: [PVarV v (BSortV v)]  -- ^ Predicate variable parameters
      , qtycType       :: ty                    -- ^ Underlying type
      , qtycFirstEqCon :: !(EqualityCtorP v ty) -- ^ The first equality constructor
      , qtycEqCons     :: [EqualityCtorP v ty]  -- ^ The remaining equality constructors
      , qtycSrcPos     :: !F.SourcePos          -- ^ Source position
      , qtycSFun       :: Maybe (SizeFunV v)    -- ^ Default termination measure
      }
    deriving (Data, Typeable, Generic, Functor, Foldable, Traversable)
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
