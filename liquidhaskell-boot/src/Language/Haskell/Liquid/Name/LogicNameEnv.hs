module Language.Haskell.Liquid.Name.LogicNameEnv
  ( LogicNameEnv
  ) where

import           Language.Fixpoint.Types
import           Language.Haskell.Liquid.Types.Names


-- | For every symbol tells the corresponding LHName and Sort
--
-- Symbols are expected to have been created by 'logicNameToSymbol'.
--
type LogicNameEnv = SEnv LHName
