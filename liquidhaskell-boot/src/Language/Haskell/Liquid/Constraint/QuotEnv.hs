module Language.Haskell.Liquid.Constraint.QuotEnv
  ( CGEqualityCtor  (..)
  , CGQuotDecl      (..)
  , CGQuotEnv
  , EqualityTerm    (..)
  ) where

import Data.HashMap.Strict                 (HashMap)

import Language.Fixpoint.Types             (Constant, Expr, Symbol)
import Language.Fixpoint.Types.Spans       (Located, SourcePos)
import Language.Haskell.Liquid.Types.RType (LocSpecType, PVar, RSort, SizeFunV, SpecType)
import Language.Haskell.Syntax.Module.Name (ModuleName)

data EqualityTerm
  = VariableP !Symbol
  | ApplyP
      { constructor :: !Symbol
      , arguments   :: ![EqualityTerm]
      }
  | ConstantP !Constant

data CGEqualityCtor
  = CGEqualityCtor
      { cgecName          :: !(Located Symbol)
      -- | ^ The name of the equality constructor
      , cgecTyParams      :: ![Symbol]
      -- | ^ Type variable parameters of the quotient type
      , cgecTyVars        :: ![Symbol]
      -- | ^ Type variables bound in the equality constructor             
      , cgecTheta         :: ![LocSpecType]
      -- | ^ Class constraints of the equality constructor
      , cgecBinds         :: !(HashMap Symbol SpecType)
      -- | ^ Bound variables of the equality constructor
      , cgecPreconditions :: ![Expr]
      -- | ^ The precondition of the equality constructor
      , cgecLeftTerm      :: !EqualityTerm
      -- | ^ The left-hand side of the constructed equality
      , cgecRightTerm     :: !EqualityTerm
      -- | ^ The right-hand side of the constructed equality
      }

data CGQuotDecl
  = CGQuotDecl
      { cgqName   :: !(Located Symbol)
      -- | ^ The name of the quotient declaration
      , cgqTyVars :: ![Symbol]
      -- | ^ Type variable parameters
      , cgqSrcPos :: !SourcePos
      -- | ^ The source position of the quotient type declaration
      , cgqPVars  :: ![PVar RSort]
      -- | ^ Predicate variable parameters
      , cgqType   :: !LocSpecType
      -- | ^ Underlying type
      , cgqEqCon  :: !CGEqualityCtor
      -- | ^ The first equality constructor
      , cgqEqCons :: ![CGEqualityCtor]
      -- | ^ The remaining equality constructors
      , cgqSFun   :: !(Maybe (SizeFunV Symbol))
      -- | ^ Default termination measure
      }

type CGQuotEnv = HashMap (ModuleName, Symbol) CGQuotDecl
