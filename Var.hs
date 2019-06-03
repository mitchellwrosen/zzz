module Var
  ( Var(..)
  , varGrammar
  ) where

import Data.Text (Text)

import Language.SexpGrammar


newtype Var
  = Var { unVar :: Text }
  deriving stock (Show)

varGrammar :: Grammar Position (Sexp :- t) (Var :- t)
varGrammar =
  symbol >>> iso Var unVar
