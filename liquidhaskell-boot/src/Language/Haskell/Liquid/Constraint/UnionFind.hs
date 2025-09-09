{-# LANGUAGE BlockArguments             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE ScopedTypeVariables        #-}

-- | A 'typed' union-find implementation
module Language.Haskell.Liquid.Constraint.UnionFind
  ( UnionFind
  , Valued (..)
  , find
  , lookup
  , union
  ) where

import           Prelude                    hiding (lookup)

import           Control.Monad              (unless)
import           Control.Monad.State.Strict (MonadState)
import qualified Control.Monad.State.Strict as State

import           Data.Functor               (($>))
import           Data.Hashable              (Hashable)
import           Data.HashMap.Internal      (Hash, HashMap)
import qualified Data.HashMap.Internal      as HashMap

newtype UnionFind k v
  = UnionFind { unionFind :: HashMap k (Link k v) }
  deriving (Semigroup, Monoid)

data Hashed k
  = Hashed
      { hash :: {-# UNPACK #-} !Hash
      , key  :: !k
      }
    deriving Show

data Valued k v
  = (:=>) !k v
  deriving Functor

data Link k v
  = Info
      { rank  :: {-# UNPACK #-} !Int
      , value :: !v
      }
    -- ^ This is the descriptive element of the equivalence class and its rank.
  | Link {-# UNPACK #-} !(Hashed k)
    -- ^ Pointer to some other element of the equivalence class.
  deriving Show

instance Eq k => Eq (Hashed k) where
  hx == hy = key hx == key hy

infix 1 :=>

find
  :: (Applicative m, Hashable k, MonadState (UnionFind k v) m)
  => (v -> v -> m v)
  -> Valued k v
  -> m k
find f = fmap key . find' f

find'
  :: forall k v m. (Hashable k, MonadState (UnionFind k v) m)
  => (v -> v -> m v)
  -> Valued k v
  -> m (Hashed k)
find' f (ik :=> v) = go Hashed { hash = HashMap.hash ik, key = ik }
  where
    go :: Hashed k -> m (Hashed k)
    go h@Hashed {hash, key} = do
      UnionFind {unionFind} <- State.get
      case HashMap.lookup' hash key unionFind of
        Nothing ->
          State.put
            ( UnionFind $ HashMap.insert' hash key Info { rank = 1, value = v } unionFind
            ) $> h
        Just Info {..} -> do
          nv <- f v value
          State.modify'
            (\(UnionFind un) ->
                UnionFind $ HashMap.insert' hash key Info { rank, value = nv } un
            ) $> h
        Just (Link h') -> do
          nh <- go h'
          State.modify'
            (\(UnionFind un) ->
                UnionFind $ HashMap.insert' hash key (Link nh) un
            ) $> nh

lookup :: forall k v. Hashable k => k -> UnionFind k v -> Maybe (Valued k v)
lookup ik UnionFind {unionFind} = go Hashed { key = ik, hash = HashMap.hash ik }
  where
    go :: Hashed k -> Maybe (Valued k v)
    go Hashed {hash, key}
      = case HashMap.lookup' hash key unionFind of
          Nothing           -> Nothing
          Just Info {value} -> Just (key :=> value)
          Just (Link h')    -> go h'

union
  :: (Hashable k, MonadState (UnionFind k v) m)
  => (v -> v -> m v)
  -> Valued k v
  -> Valued k v
  -> m ()
union f x y = do
  hx <- find' f x
  hy <- find' f y
  unless (hx == hy) do
    UnionFind {unionFind} <- State.get
    case (HashMap.lookup' (hash hx) (key hx) unionFind, HashMap.lookup' (hash hy) (key hy) unionFind) of
      (Just ix@Info {}, Just iy@Info {}) -> do
        nvalue <- f (value ix) (value iy)
        let (nroot, nchild, nrank) =
              case compare (rank ix) (rank iy) of
                GT -> (hx, hy, rank ix)
                LT -> (hy, hx, rank iy)
                EQ -> (hx, hy, rank ix + 1)
        State.put $ UnionFind
          $ HashMap.insert' (hash nroot) (key nroot) Info { rank = nrank, value = nvalue }
          $ HashMap.insert' (hash nchild) (key nchild) (Link nroot) unionFind
      _ -> error "UnionFind.union: discovered a root that was not an Info node"
