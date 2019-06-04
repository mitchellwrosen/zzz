module Zzz.Syntax.Function
  ( Function(..)
  ) where

import Data.Text (Text)


newtype Function
  = Function { unFunction :: Text }
  deriving stock (Show)
