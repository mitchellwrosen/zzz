module Sort where

import Data.Hashable (Hashable)
import GHC.Generics (Generic)


data Sort
  = SortArray Sort Sort
  | SortBool
  | SortInt
  deriving stock (Eq, Generic, Show)
  deriving anyclass (Hashable)

arraySort :: Sort -> Sort -> Sort
arraySort =
  SortArray

boolSort :: Sort
boolSort =
  SortBool

intSort :: Sort
intSort =
  SortInt
