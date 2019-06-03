module Sort where

import Data.Hashable (Hashable)
import GHC.Generics (Generic)


data Sort
  = SortBool
  | SortInt
  deriving stock (Eq, Generic, Show)
  deriving anyclass (Hashable)

boolSort :: Sort
boolSort =
  SortBool

intSort :: Sort
intSort =
  SortInt
