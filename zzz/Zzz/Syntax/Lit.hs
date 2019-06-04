module Zzz.Syntax.Lit
  ( Lit(..)
  , litGrammar
  , compileLit
  ) where

import Control.Effect
import Language.SexpGrammar
import Z3.Effect (AST, Z3)

import qualified Z3.Effect as Z3


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

compileLit ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Lit
  -> m AST
compileLit = \case
  LitBool b ->
    if b then Z3.mkTrue else Z3.mkFalse

  LitInt n ->
    Z3.mkInteger n
