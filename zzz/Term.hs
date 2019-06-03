module Term where

import Function (Function(..))
import Lit (Lit(..))
import Var (Var)

import qualified Lit (litGrammar)
import qualified Var (varGrammar)

import Data.List (foldl')
import Data.Text (Text)
import Language.SexpGrammar

import qualified Data.ByteString.Lazy as ByteString.Lazy
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text


data Term
  = Add [Term]
  | And [Term]
  | Apply Function [Term]
  | Distinct [Term]
  | Eq Term Term
  | Ge Term Term
  | Gt Term Term
  | Iff Term Term
  | Implies Term Term
  | Ite Term Term Term
  | Le Term Term
  | Lit Lit
  | Lt Term Term
  | Negate Term
  | Mul [Term]
  | Or [Term]
  | Not Term
  | Sub [Term]
  | Var Var
  | Xor Term Term
  deriving stock (Show)

  -- div
  -- mod
  -- rem
  -- int2real
  -- real2int
  -- isInt

instance Num Term where
  abs e =
    Ite (e >=. 0) e (negate e)

  fromInteger =
    Lit . LitInt

  negate =
    Negate

  signum e =
    Ite (Gt e 0) 1 0

  e1 + e2 =
    Add [e1, e2]

  e1 * e2 =
    Mul [e1, e2]

  e1 - e2 =
    Sub [e1, e2]


infix 4 =.
(=.) :: Term -> Term -> Term
(=.) =
  Eq

infixr 2 ||.
(||.) :: Term -> Term -> Term
e1 ||. e2 =
  Or [e1, e2]

infixr 3 &&.
(&&.) :: Term -> Term -> Term
e1 &&. e2 =
  And [e1, e2]

infix 4 <.
(<.) :: Term -> Term -> Term
(<.) =
  Lt

infix 4 <=.
(<=.) :: Term -> Term -> Term
(<=.) =
  Le

infix 4 >.
(>.) :: Term -> Term -> Term
(>.) =
  Gt

infix 4 >=.
(>=.) :: Term -> Term -> Term
(>=.) =
  Ge

false :: Term
false =
  Lit (LitBool False)

true :: Term
true =
  Lit (LitBool True)

not :: Term -> Term
not =
  Not

xor :: Term -> Term -> Term
xor =
  Xor

iff :: Term -> Term -> Term
iff =
  Iff

implies :: Term -> Term -> Term
implies =
  Implies

ite :: Term -> Term -> Term -> Term
ite =
  Ite

distinct :: [Term] -> Term
distinct =
  Distinct

apply :: Function -> [Term] -> Term
apply =
  Apply

parseTerm :: String -> Either String Term
parseTerm =
  Text.pack >>>
  Text.encodeUtf8 >>>
  ByteString.Lazy.fromStrict >>>
  decodeWith termGrammar ""

termGrammar :: Grammar Position (Sexp :- t) (Term :- t)
termGrammar =
  andGrammar <>
  addGrammar <>
  eqGrammar <>
  geGrammar <>
  gtGrammar <>
  iteGrammar <>
  leGrammar <>
  (Lit.litGrammar >>> litGrammar) <>
  ltGrammar <>
  mulGrammar <>
  notGrammar <>
  orGrammar <>
  subGrammar <>
  xorGrammar <>
  (Var.varGrammar >>> varGrammar) <>
  applyGrammar

  where
    andGrammar :: Grammar Position (Sexp :- t) (Term :- t)
    andGrammar =
      varargGrammar
        "and"
        And
        (\case
          And es -> Right es
          _ -> Left (expected "And"))

    addGrammar :: Grammar Position (Sexp :- t) (Term :- t)
    addGrammar =
      varargGrammar
        "+"
        Add
        (\case
          Add es -> Right es
          _ -> Left (expected "Add"))

    applyGrammar :: Grammar Position (Sexp :- t) (Term :- t)
    applyGrammar =
      list (el symbol >>> rest termGrammar) >>>
      pair >>>
      partialIso
        (\(name, args) -> Apply (Function name) args)
        (\case
          Apply f es -> Right (unFunction f, es)
          _ -> Left (expected "Apply"))

    eqGrammar :: Grammar Position (Sexp :- t) (Term :- t)
    eqGrammar =
      varargGrammar'
        "="
        Eq
        (\case
          Eq e1 e2 -> Right [e1, e2]
          _ -> Left (expected "Eq"))

    geGrammar :: Grammar Position (Sexp :- t) (Term :- t)
    geGrammar =
      binopGrammar
        ">="
        Ge
        (\case
          Ge e1 e2 -> Right (e1, e2)
          _ -> Left (expected "Ge"))

    gtGrammar :: Grammar Position (Sexp :- t) (Term :- t)
    gtGrammar =
      binopGrammar
        ">"
        Gt
        (\case
          Gt e1 e2 -> Right (e1, e2)
          _ -> Left (expected "Gt"))

    iteGrammar :: Grammar Position (Sexp :- t) (Term :- t)
    iteGrammar =
      list (el (sym "ite") >>> el termGrammar >>> el termGrammar >>> el termGrammar) >>>
      pair >>>
      pair >>>
      partialIso
        (\(e1, (e2, e3)) -> Ite e1 e2 e3)
        (\case
          Ite e1 e2 e3 -> Right (e1, (e2, e3))
          _ -> Left (expected "Ite"))

    leGrammar :: Grammar Position (Sexp :- t) (Term :- t)
    leGrammar =
      binopGrammar
        "<="
        Le
        (\case
          Le e1 e2 -> Right (e1, e2)
          _ -> Left (expected "Le"))

    litGrammar :: Grammar Position (Lit :- t) (Term :- t)
    litGrammar =
      partialIso
        Lit
        (\case
          Lit lit -> Right lit
          _ -> Left (expected "Lit"))

    ltGrammar :: Grammar Position (Sexp :- t) (Term :- t)
    ltGrammar =
      binopGrammar
        "<"
        Lt
        (\case
          Lt e1 e2 -> Right (e1, e2)
          _ -> Left (expected "Lt"))

    mulGrammar :: Grammar Position (Sexp :- t) (Term :- t)
    mulGrammar =
      varargGrammar
        "*"
        Mul
        (\case
          Mul es -> Right es
          _ -> Left (expected "Mul"))

    notGrammar :: Grammar Position (Sexp :- t) (Term :- t)
    notGrammar =
      unopGrammar
        "not"
        Not
        (\case
          Not e -> Right e
          _ -> Left (expected "Not"))

    orGrammar :: Grammar Position (Sexp :- t) (Term :- t)
    orGrammar =
      varargGrammar
        "or"
        Or
        (\case
          Or es -> Right es
          _ -> Left (expected "Or"))

    subGrammar :: Grammar Position (Sexp :- t) (Term :- t)
    subGrammar =
      varargGrammar
        "-"
        Sub
        (\case
          Sub es -> Right es
          _ -> Left (expected "Sub"))

    varGrammar :: Grammar Position (Var :- t) (Term :- t)
    varGrammar =
      partialIso
        Var
        (\case
          Var var -> Right var
          _ -> Left (expected "Var"))

    xorGrammar :: Grammar Position (Sexp :- t) (Term :- t)
    xorGrammar =
      varargGrammar'
        "xor"
        Xor
        (\case
          Xor e1 e2 -> Right [e1, e2]
          _ -> Left (expected "Xor"))

    unopGrammar ::
         Text
      -> (Term -> Term)
      -> (Term -> Either Mismatch Term)
      -> Grammar Position (Sexp :- t) (Term :- t)
    unopGrammar s f p =
      list (el (sym s) >>> el termGrammar) >>>
      partialIso f p

    binopGrammar ::
         Text
      -> (Term -> Term -> Term)
      -> (Term -> Either Mismatch (Term, Term))
      -> Grammar Position (Sexp :- t) (Term :- t)
    binopGrammar s f p =
      list (el (sym s) >>> el termGrammar >>> el termGrammar) >>>
      pair >>>
      partialIso (uncurry f) p

    varargGrammar ::
         Text
      -> ([Term] -> Term)
      -> (Term -> Either Mismatch [Term])
      -> Grammar Position (Sexp :- t) (Term :- t)
    varargGrammar s f p =
      list (el (sym s) >>> rest termGrammar) >>>
      partialIso f p

    varargGrammar' ::
         Text
      -> (Term -> Term -> Term)
      -> (Term -> Either Mismatch [Term])
      -> Grammar Position (Sexp :- t) (Term :- t)
    varargGrammar' s f p =
      list (el (sym s) >>> rest termGrammar) >>>
      partialIso
        (\case
          [] -> error ("parseTerm: empty " ++ Text.unpack s)
          [_] -> error ("parseTerm: singleton " ++ Text.unpack s)
          x:xs -> foldl' f x xs)
        p
