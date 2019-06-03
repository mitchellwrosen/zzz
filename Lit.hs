module Lit
  ( Lit(..)
  , litGrammar
  ) where

import Language.SexpGrammar


data Lit
  = LitBool Bool
  | LitInt Integer
  deriving stock (Show)

litGrammar :: Grammar Position (Sexp :- t) (Lit :- t)
litGrammar =
  (sexpIso >>> litBoolGrammar) <>
  (integer >>> litIntGrammar)

  where
    litBoolGrammar :: Grammar Position (Bool :- t) (Lit :- t)
    litBoolGrammar =
      partialIso
        LitBool
        (\case
          LitBool b -> Right b
          _ -> Left (expected "LitBool"))

    litIntGrammar :: Grammar Position (Integer :- t) (Lit :- t)
    litIntGrammar =
      partialIso
        LitInt
        (\case
          LitInt n -> Right n
          _ -> Left (expected "LitInt"))
