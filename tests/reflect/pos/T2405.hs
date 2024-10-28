{-# OPTIONS_GHC -O #-}

{-@ LIQUID "--reflection" @-}

module T2405 where

{-@ reflect singleton @-}
singleton :: a -> [a]
singleton x = [x]
