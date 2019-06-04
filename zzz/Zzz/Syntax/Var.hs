module Zzz.Syntax.Var
  ( Var(..)
  , varGrammar
  ) where

import Zzz.Prelude

import Data.Hashable (Hashable)
import Data.Text (Text)
import Language.SexpGrammar


newtype Var
  = Var { unVar :: Text }
  deriving stock (Eq, Show)
  deriving newtype (Hashable)

varGrammar :: Grammar Position (Sexp :- t) (Var :- t)
varGrammar =
  symbol >>> iso Var unVar
