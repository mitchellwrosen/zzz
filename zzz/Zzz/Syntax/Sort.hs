module Zzz.Syntax.Sort
  ( Sort(..)
  , arraySort
  , boolSort
  , intSort
  , compileSort
  ) where

import Zzz.Prelude

import Control.Effect
import Data.Hashable (Hashable)
import Z3.Effect (Z3)

import qualified Z3.Effect as Z3


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

compileSort ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Sort
  -> m Z3.Sort
compileSort = \case
  SortArray s1 s2 -> do
    s1' <- compileSort s1
    s2' <- compileSort s2
    Z3.mkArraySort s1' s2'

  SortBool ->
    Z3.mkBoolSort

  SortInt ->
    Z3.mkIntSort
