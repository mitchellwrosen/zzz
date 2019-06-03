module Function
  ( Function(..)
  ) where

import Sort (Sort)

import Data.Hashable (Hashable)
import Data.Text (Text)
import GHC.Generics (Generic)


data Function
  = Function Text [Sort] Sort
  deriving stock (Eq, Generic, Show)
  deriving anyclass (Hashable)
