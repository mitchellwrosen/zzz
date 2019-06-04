module Zzz
  ( Zzz
  , ZzzC
  , runZzz
    -- * Solver
  , assert
  -- , frame
  , check
  -- , getModel
  , printModel
  -- , modelToString
    -- * Simplifier
  -- , simplify
    -- * Declarations
  , declare
  -- , declareFunction
  , Function
    -- * Terms
  , Term(..)
  , (=.)
  , false
  , true
  , Term.not
  , (||.)
  , (&&.)
  , xor
  , iff
  , implies
  , ite
  , distinct
  , (<.)
  , (<=.)
  , (>.)
  , (>=.)
  , apply
    -- * Sorts
  , Sort
  , boolSort
  , intSort
  ) where

import Function
import Sort
import Term
import Zzz.Effect (Zzz, assert, declare)
import Zzz.Carrier (ZzzC, runZzz)

import Control.Category ((>>>))
import Control.Effect
import Control.Monad.IO.Class (MonadIO(..))
import Data.Foldable (traverse_)
import Z3.Effect (Z3, Model, Result)

import qualified Z3.Effect as Z3


printModel ::
     ( Carrier sig m
     , Member Z3 sig
     , MonadIO m
     )
  => Model
  -> m ()
printModel model = do
  string <- Z3.modelToString model
  traverse_ (putStrLn >>> liftIO) (lines string)

check ::
     ( Carrier sig m
     , Member Z3 sig
     , MonadIO m
     )
  => m Result
check =
  Z3.solverCheck
