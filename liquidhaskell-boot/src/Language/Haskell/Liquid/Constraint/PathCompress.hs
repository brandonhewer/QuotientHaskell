{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE BlockArguments             #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TupleSections              #-}

-- | Substitution maps with path compression, defined over HashMaps from the containers package.
module Language.Haskell.Liquid.Constraint.PathCompress
  ( PathCompress    (..)
  , PathTrace       (..)
  , PathTraceST     (..)
  , Step            (..)
  , UnionState      (..)
  , UnionMap
  , findWithPath
  , insertWithPath
  , insertWithPathST
  ) where

import           Control.Monad.State.Strict (StateT)
import qualified Control.Monad.State.Strict as State
import           Data.Functor               (($>))
import           Data.Hashable              (Hashable)
import           Data.HashMap.Internal      (Hash, HashMap)
import qualified Data.HashMap.Internal      as HashMapI

newtype UnionMap k v
  = UnionMap { unionMap :: HashMap k v }
  deriving (Semigroup, Monoid)

data Step k v a
  = Continue k a
  | Done v

newtype InsertNewStrategy k v
  = InsertNewStrategy
      { insertNew :: Hash -> k -> v -> HashMap k v -> HashMap k v
      }

data PathNode k a
  = PathNode
      { nodeHash :: !Hash
      , nodeKey  :: !k
      , nodeReft :: !a
      }

data UnionState s k v
  = UnionState
      { unionState   :: !s
        -- | ^ Threaded user state.
      , unionFindMap :: !(UnionMap k v) 
        -- | ^ The union map over which to perform path compression.
      }

data PathCompress k v m a
  = PathCompress
      { step       :: k -> v -> StateT (UnionMap k v) m (Step k v a)
        -- | ^ The step function permits intermediate operations on the union map structure.
      , base       :: k -> m v
        -- | ^ Handles the case where path compression ends at a variable.
      , accumulate :: a -> a -> a
        -- | ^ Accumulates additional structure on variables in the UnionMap structure.
        --
        --     For example, a UnionMap that maps type variables to types might contain:
        --                  { α => {β | r1}, β => {γ | r2}, γ => τ }
        --     When we fully compress the paths we end up with:
        --                  { α => {τ | r1 and r2}, β => {τ | r2}, γ => τ }
      , refine     :: a -> v -> v
        -- | ^ Constructs a new node value using accumulated structure along a path.
      }

data PathCompressST s k v m a
  = PathCompressST
      { stepST       :: k -> v -> StateT (UnionState s k v) m (Step k v a)
      , baseST       :: k -> StateT s m v
      , accumulateST :: a -> a -> a
      , refineST     :: a -> v -> v
      }

data PathTrace k v m a
  = PathTrace
      { stepTrace       :: [k] -> v -> StateT (UnionMap k v) m (Step k v a)
      , baseTrace       :: k -> m v
      , accumulateTrace :: a -> a -> a
      , refineTrace     :: a -> v -> v
      }

data PathTraceST s k v m a
  = PathTraceST
      { stepTraceST       :: [k] -> v -> StateT (UnionState s k v) m (Step k v a)
      , baseTraceST       :: s -> k -> m v
      , accumulateTraceST :: a -> a -> a
      , refineTraceST     :: a -> v -> v
      }

-- | A generic union-find algorithm with path compression and cycle detection.
--
--   Required preconditions for genericCompress f pc k m:
--     > The HashMap `m` must be finite
--     > if `step k pc = Continue k' x` then `k /= k'`, i.e. `m` contains no 1-step cycles
genericCompress
  :: (Monad m, Eq k, Hashable k)
  => InsertNewStrategy k v
  -> PathCompress k v m a
  -> k
  -> StateT (UnionMap k v) m v
genericCompress InsertNewStrategy {..} PathCompress {..} ik
  = State.StateT \m@UnionMap {unionMap = um} ->
      let !hk = HashMapI.hash ik
       in case HashMapI.lookup' hk ik um of
            Nothing -> (\v -> (v, UnionMap $ insertNew hk ik v um)) <$> base ik
            Just v -> State.runStateT (step ik v) m >>= \case
              (Done     !v'   , m') -> pure (v', UnionMap $ insertNew hk ik v $ unionMap m')
              (Continue !k' !a, m') -> State.runStateT (walkPath (PathNode hk ik a) [] k' v) m'
  where
    -- | Paths are constructed backwards, and thus a left fold accumulates intermediates.
    walkPath p@PathNode {nodeKey, nodeReft} path k kv = do
      let !hk = HashMapI.hash k
      UnionMap {unionMap} <- State.get
      case HashMapI.lookup' hk k unionMap of
        Nothing -> do
          let (af, mf) = compressPath p path kv unionMap
          v <- State.lift $ base k
          State.put (UnionMap $ insertNew hk k v mf) $> refine af v
        Just v -> step k v >>= \case
          Done !v' -> do
            let (af, mf) = compressPath p path v' unionMap
                vf       = refine af v'
            State.put (UnionMap $ insertNew hk k vf mf) $> vf
          Continue !k' !a
            | isCyclic path nodeKey k' ->
                let nm  = HashMapI.delete' hk k unionMap
                    !af = foldl' (\al (PathNode _ _ ar) -> accumulate al ar) (accumulate nodeReft a) path
                    nv  = refine af kv
                    mf  = foldl' (\m' (PathNode nh nk _) -> HashMapI.insert' nh nk nv m') nm path
                  in State.put (UnionMap mf) $> nv
            | otherwise           ->
                walkPath PathNode
                  { nodeHash = hk
                  , nodeKey  = k
                  , nodeReft = a
                  } (p : path) k' v

    isCyclic path pk k = pk == k || any (\(PathNode _ nk _) -> nk == k) path

    accumulateAndInsert v (!a', !m') PathNode {nodeHash, nodeKey, nodeReft}
      = (accumulate a' nodeReft, HashMapI.insert' nodeHash nodeKey (refine a' v) m')

    compressPath PathNode {nodeHash, nodeKey, nodeReft} path v im
      = foldl' (accumulateAndInsert v) (nodeReft, HashMapI.insert' nodeHash nodeKey v im) path

-- | Lookup into a map union structure.
findAndCompress
  :: (Monad m, Eq k, Hashable k)
  => PathCompress k v m a
  -> k
  -> UnionMap k v
  -> m (v, UnionMap k v)
findAndCompress p k = State.runStateT $ genericCompress (InsertNewStrategy \_ _ _ m -> m) p k

-- | Insertion into a map union structure.
insertAndCompress
  :: (Monad m, Eq k, Hashable k)
  => PathCompress k v m a
  -> k
  -> UnionMap k v
  -> m (v, UnionMap k v)
insertAndCompress p k = State.runStateT $ genericCompress (InsertNewStrategy HashMapI.insert') p k

-- | Generic path compression with threaded state over a union map structure.
genericCompressST
  :: (Monad m, Eq k, Hashable k)
  => InsertNewStrategy k v
  -> PathCompressST s k v m a
  -> s
  -> k
  -> UnionMap k v
  -> m (v, UnionMap k v, s)
genericCompressST ins PathCompressST {..} s k m
  = flatten <$> State.runStateT
      ( State.runStateT
          ( genericCompress ins PathCompress
              { step
              , base       = baseST
              , accumulate = accumulateST
              , refine     = refineST
              } k
          ) m
      ) s
  where
    flatten ((x, y), z) = (x, y, z)

    step nk nv
      = State.StateT \unionFindMap -> State.StateT \unionState ->
          (\(sp, UnionState us um) -> ((sp, um), us))
            <$> State.runStateT (stepST nk nv) UnionState {..}

-- | Insertion into a union map with threaded state.
insertAndCompressST
  :: (Monad m, Eq k, Hashable k)
  => PathCompressST s k v m a
  -> s
  -> k
  -> UnionMap k v
  -> m (v, UnionMap k v, s)
insertAndCompressST = genericCompressST $ InsertNewStrategy HashMapI.insert'

withTrace :: Monad m => PathTrace k v m a -> PathCompress k v (StateT [k] m) a
withTrace PathTrace {..}
  = PathCompress
      { step       = \k' v -> do
          ks <- State.lift State.get
          let ks' = k' : ks
          State.mapStateT State.lift (stepTrace ks' v) <* State.lift (State.put ks')
      , base       = State.lift . baseTrace
      , accumulate = accumulateTrace
      , refine     = refineTrace
      }

stateMap :: Functor m => (s -> s') -> (s -> s' -> s) -> StateT s' m a -> StateT s m a
stateMap focus update (State.StateT k)
  = State.StateT \s -> fmap (update s) <$> k (focus s)

mapUnionState :: (s -> s') -> UnionState s k v -> UnionState s' k v
mapUnionState f us@UnionState {unionState} = us { unionState = f unionState }

liftOnKeys :: Functor m => StateT (UnionState s k v) m a -> StateT (UnionState (s, b) k v) m a
liftOnKeys = stateMap (mapUnionState fst) \UnionState {unionState = (_,b)} -> mapUnionState (,b)

withTraceST :: Monad m => PathTraceST s k v m a -> PathCompressST (s, [k]) k v m a
withTraceST PathTraceST {..}
  = PathCompressST
      { stepST       = \k' v -> do
          (_, ks) <- State.gets unionState
          let ks' = k' : ks
          liftOnKeys (stepTraceST ks' v) <* State.modify' (mapUnionState $ fmap $ const ks')
      , baseST       = \k -> State.gets fst >>= State.lift . (`baseTraceST` k)
      , accumulateST = accumulateTraceST
      , refineST     = refineTraceST
      }

-- | Insertion into a union map with a path trace.
insertWithPath
  :: (Monad m, Eq k, Hashable k)
  => PathTrace k v m a
  -> k
  -> UnionMap k v
  -> m (v, UnionMap k v)
insertWithPath t k = flip State.evalStateT [] . insertAndCompress (withTrace t) k

-- | Insertion into a union map with both a path trace and threaded state.
insertWithPathST
  :: (Monad m, Eq k, Hashable k)
  => PathTraceST s k v m a
  -> s
  -> k
  -> UnionMap k v
  -> m (v, UnionMap k v, s)
insertWithPathST t s k = fmap dropKeys . insertAndCompressST (withTraceST t) (s, []) k
  where dropKeys (x, y, (z, _)) = (x, y, z)

-- | Lookup into a union map with a path trace.
findWithPath
  :: (Monad m, Eq k, Hashable k)
  => PathTrace k v m a
  -> k
  -> UnionMap k v
  -> m (v, UnionMap k v)
findWithPath t k = flip State.evalStateT [] . findAndCompress (withTrace t) k
