{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE NamedFieldPuns    #-}

module Language.Haskell.Liquid.Constraint.NBETypes where

import           Data.HashMap.Strict                      (HashMap)
import           Data.HashSet                             (HashSet)
import           Data.Hashable                            (Hashable)
import qualified Data.Hashable                            as Hash

import Language.Fixpoint.Types       (Expr, LocSymbol, QPattern, Symbol)
import Language.Haskell.Liquid.Types (RTyVar, SpecQuotient, SpecType)

data QDataCons
  = QDataCons
      { qdcUnderlyingTyCon :: !Symbol
      , qdcUnderlyingName  :: !Symbol
      , qdcUnderlyingType  :: !SpecType
      , qdcRefinedTypes    :: !(HashMap Symbol SpecType)
      } deriving Show

data QuotientRewrite
  = QuotientRewrite
      { rwPattern      :: !QPattern
        -- | ^ The pattern to check for unification with when deciding whether to rewrite
        --     an expression
      , rwExpr         :: !Expr
        -- | ^ The expression to rewrite to after applying the unifying substitution
      , rwPrecondition :: !(Maybe Expr)
        -- | ^ The precondition for when this rewrite rule should be applied
      , rwFreeVars     :: !(HashSet Symbol)
        -- | ^ The free variables that appear in rwPattern and rwExpr
      } deriving Show

data QuotientTypeDef
  = QuotientTypeDef
      { qtdName     :: !LocSymbol
      , qtdType     :: !SpecType
      , qtdQuots    :: ![SpecQuotient]
      , qtdRewrites :: ![QuotientRewrite]
      , qtdTyVars   :: ![RTyVar]
      , qtdArity    :: !Int
      }

-- | Typed definitions in the environment
data NBEDefinition
  = NBEDefinition
      { nbeType        :: !SpecType -- | Type of the definition
      , nbeDefinition  :: !Expr     -- | Body of the definition
      , nbeIsRecursive :: !Bool     -- | Whether this definition is recursively defined
      } deriving Show

data NBEDataCons
  = NBEDataCons
      { nbeDataConEnv     :: !(HashMap Symbol SpecType)
      , nbeQuotDataConEnv :: !(HashMap Symbol QDataCons)
      }

-- | Environment for normalisation by evaluation
data NBEEnv
  = NBE
      { nbeDefs          :: !(HashMap Symbol NBEDefinition)
        -- | ^ Definitions that can be unfolded
      , nbeSelectors     :: !(HashMap Symbol (Symbol, Int))
        -- | ^ Selectors such that a selector symbol maps to its data constructor
        --     and projection index.
      , nbeDataCons      :: !NBEDataCons
        -- | ^ Reflected data constructors.
      , nbeGuards        :: ![Expr]
        -- | ^ List of (normalised) axioms in scope.
      , nbeQuotientTypes :: !(HashMap Symbol QuotientTypeDef)
        -- | ^ List of rewrite rules that can be applied, map from Quotient TyCon.
      , nbeUnfoldTypes   :: !(HashMap Symbol UnfoldType)
        -- | ^ The unfold type for the definitions in scope
      }

data BinderType
  = KnownType !SpecType
  | UnknownType

-- | Describes how many times a recursive definition can be reduced
data UnfoldType
  = LimitedUnfold !Int
  | CompleteUnfold

data TypedThing
  = BoundVariable    !SpecType
  | Definition       !NBEDefinition
  | QDataConstructor !QDataCons
  | DataConstructor  !SpecType

data NBEState
  = NBEState
      { nbeBinds      :: !(HashMap Symbol BinderType)
        -- | ^ The bindings in scope (cannot be unfolded) with possibly discovered types.
        --     Act as free variables in open terms for the purpose of rewriting.
      , nbeNormalDefs :: !(HashMap Symbol (NBEResult Expr))
        -- | ^ Computed normalisation results for non-recursive definitions
      }

data ArgNormalisation
  = NoNormalisation
  | UntypedNormalisation
  | TypedNormalisation [SpecType]

-- | The result of rewriting, with a possible precondition that must hold for this
--   rewrite result to be applicable.
data RewriteResult a
  = RWResult
      { rwCondition   :: !(Maybe Expr)
      -- | ^ The precondition that must hold before this rewrite is applicable
      , rwResult      :: !a
      -- | ^ The rewritten expression
      , rwQuantifiers :: !(HashSet Symbol)
      -- | ^ The free variables in rwResult/rwCondition that should be quantified over
      } deriving (Functor, Show)

newtype NBEResult a
  = NBEResult [RewriteResult a]
    deriving (Foldable, Functor, Show, Traversable)

instance Semigroup NBEDataCons where
  ndc1 <> ndc2
    = NBEDataCons
        { nbeDataConEnv     = nbeDataConEnv     ndc1 <> nbeDataConEnv     ndc1
        , nbeQuotDataConEnv = nbeQuotDataConEnv ndc1 <> nbeQuotDataConEnv ndc2
        }

instance Monoid NBEDataCons where
  mempty
    = NBEDataCons
        { nbeDataConEnv     = mempty
        , nbeQuotDataConEnv = mempty
        }

instance Semigroup NBEEnv where
  nenv1 <> nenv2
    = NBE
        { nbeDefs          = nbeDefs          nenv1 <> nbeDefs          nenv2
        , nbeSelectors     = nbeSelectors     nenv1 <> nbeSelectors     nenv2
        , nbeDataCons      = nbeDataCons      nenv1 <> nbeDataCons      nenv2
        , nbeGuards        = nbeGuards        nenv1 <> nbeGuards        nenv2
        , nbeQuotientTypes = nbeQuotientTypes nenv1 <> nbeQuotientTypes nenv2
        , nbeUnfoldTypes   = nbeUnfoldTypes   nenv1 <> nbeUnfoldTypes   nenv2
        }

instance Monoid NBEEnv where
  mempty
    = NBE
        { nbeDefs          = mempty
        , nbeSelectors     = mempty
        , nbeDataCons      = mempty
        , nbeGuards        = mempty
        , nbeQuotientTypes = mempty
        , nbeUnfoldTypes   = mempty
        }

instance Semigroup NBEState where
  nst1 <> nst2
    = NBEState
        { nbeBinds      = nbeBinds      nst1 <> nbeBinds      nst2
        , nbeNormalDefs = nbeNormalDefs nst1 <> nbeNormalDefs nst2
        }

instance Monoid NBEState where
  mempty
    = NBEState
        { nbeBinds      = mempty
        , nbeNormalDefs = mempty
        }

instance Eq a => Eq (RewriteResult a) where
  r1 == r2
    =  rwCondition r1 == rwCondition r2
    && rwResult    r1 == rwResult r2

instance Hashable a => Hashable (RewriteResult a) where
  hashWithSalt n RWResult {..}
    = Hash.hashWithSalt (Hash.hashWithSalt n rwCondition) rwResult

instance Semigroup (NBEResult a) where
  NBEResult as <> NBEResult bs = NBEResult (as <> bs)

instance Monoid (NBEResult a) where
  mempty = NBEResult []

instance Foldable RewriteResult where
  foldr f z RWResult { rwResult } = f rwResult z

instance Traversable RewriteResult where
  traverse f RWResult {..} = g <$> f rwResult
    where
      g b
        = RWResult
            { rwCondition
            , rwQuantifiers
            , rwResult = b
            }

instance Semigroup ArgNormalisation where
  UntypedNormalisation <> t = t
  t <> UntypedNormalisation = t
  _ <> NoNormalisation      = NoNormalisation
  NoNormalisation <> _      = NoNormalisation
  TypedNormalisation ts <> TypedNormalisation us
    = TypedNormalisation (extend ts us)
      where
        extend :: [a] -> [a] -> [a]
        extend []       xs       = xs
        extend xs       []       = xs
        extend (x : xs) (_ : ys) = x : extend xs ys

instance Monoid ArgNormalisation where
  mempty = UntypedNormalisation
