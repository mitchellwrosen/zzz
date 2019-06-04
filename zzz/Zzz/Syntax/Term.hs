module Zzz.Syntax.Term
  ( Term(..)
  , (=.)
  , (||.)
  , (&&.)
  , (<.)
  , (<=.)
  , (>.)
  , (>=.)
  , apply
  , distinct
  , false
  , iff
  , implies
  , ite
  , Zzz.Syntax.Term.not
  , store
  , true
  , xor
    -- * Parsing
  , parseTerm
  , termGrammar
    -- * Compiling
  , compileTerm
  ) where

import Zzz.Effect (Zzz, getFunction, getVar)
import Zzz.Syntax.Function (Function(..))
import Zzz.Syntax.Lit (Lit(..), compileLit)
import Zzz.Syntax.Var (Var)
import Zzz.Types (Term(..))

import qualified Zzz.Syntax.Lit as Lit (litGrammar)
import qualified Zzz.Syntax.Var as Var (varGrammar)

import Control.Effect
import Data.List (foldl')
import Data.Text (Text)
import Language.SexpGrammar
import Z3.Effect (Z3)

import qualified Data.ByteString.Lazy as ByteString.Lazy
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import qualified Z3.Effect as Z3



infix 4 =.
(=.) :: Term -> Term -> Term
(=.) =
  Eq

infixr 2 ||.
(||.) :: Term -> Term -> Term
t1 ||. t2 =
  Or [t1, t2]

infixr 3 &&.
(&&.) :: Term -> Term -> Term
t1 &&. t2 =
  And [t1, t2]

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

store :: Term -> Term -> Term -> Term
store =
  Store

parseTerm :: String -> Either String Term
parseTerm =
  Text.pack >>>
  Text.encodeUtf8 >>>
  ByteString.Lazy.fromStrict >>>
  decodeWith termGrammar ""

termGrammar :: Grammar Position (Sexp :- t) (Term :- t)
termGrammar =
  addGrammar <>
  andGrammar <>
  distinctGrammar <>
  eqGrammar <>
  geGrammar <>
  gtGrammar <>
  impliesGrammar <>
  iteGrammar <>
  leGrammar <>
  (Lit.litGrammar >>> litGrammar) <>
  ltGrammar <>
  mulGrammar <>
  notGrammar <>
  orGrammar <>
  storeGrammar <>
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
          And ts -> Right ts
          _ -> Left (expected "And"))

    addGrammar :: Grammar Position (Sexp :- t) (Term :- t)
    addGrammar =
      varargGrammar
        "+"
        Add
        (\case
          Add ts -> Right ts
          _ -> Left (expected "Add"))

    applyGrammar :: Grammar Position (Sexp :- t) (Term :- t)
    applyGrammar =
      list (el symbol >>> rest termGrammar) >>>
      pair >>>
      partialIso
        (\(name, args) -> Apply (Function name) args)
        (\case
          Apply f ts -> Right (unFunction f, ts)
          _ -> Left (expected "Apply"))

    distinctGrammar :: Grammar Position (Sexp :- t) (Term :- t)
    distinctGrammar =
      varargGrammar
        "distinct"
        Distinct
        (\case
          Distinct ts -> Right ts
          _ -> Left (expected "Distinct"))

    eqGrammar :: Grammar Position (Sexp :- t) (Term :- t)
    eqGrammar =
      varargGrammar'
        "="
        Eq
        (\case
          Eq t1 t2 -> Right [t1, t2]
          _ -> Left (expected "Eq"))

    geGrammar :: Grammar Position (Sexp :- t) (Term :- t)
    geGrammar =
      binopGrammar
        ">="
        Ge
        (\case
          Ge t1 t2 -> Right (t1, t2)
          _ -> Left (expected "Ge"))

    gtGrammar :: Grammar Position (Sexp :- t) (Term :- t)
    gtGrammar =
      binopGrammar
        ">"
        Gt
        (\case
          Gt t1 t2 -> Right (t1, t2)
          _ -> Left (expected "Gt"))

    impliesGrammar :: Grammar Position (Sexp :- t) (Term :- t)
    impliesGrammar =
      go "=>" <> go "implies"

      where
        go s =
          binopGrammar
            s
            Implies
            (\case
              Implies t1 t2 -> Right (t1, t2)
              _ -> Left (expected "=> or implies"))

    iteGrammar :: Grammar Position (Sexp :- t) (Term :- t)
    iteGrammar =
      trinopGrammar
        "ite"
        Ite
        (\case
          Ite t1 t2 t3 -> Right (t1, (t2, t3))
          _ -> Left (expected "Ite"))

    leGrammar :: Grammar Position (Sexp :- t) (Term :- t)
    leGrammar =
      binopGrammar
        "<="
        Le
        (\case
          Le t1 t2 -> Right (t1, t2)
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
          Lt t1 t2 -> Right (t1, t2)
          _ -> Left (expected "Lt"))

    mulGrammar :: Grammar Position (Sexp :- t) (Term :- t)
    mulGrammar =
      varargGrammar
        "*"
        Mul
        (\case
          Mul ts -> Right ts
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
          Or ts -> Right ts
          _ -> Left (expected "Or"))

    storeGrammar :: Grammar Position (Sexp :- t) (Term :- t)
    storeGrammar =
      trinopGrammar
        "store"
        Store
        (\case
          Store t1 t2 t3 -> Right (t1, (t2, t3))
          _ -> Left (expected "Store"))

    subGrammar :: Grammar Position (Sexp :- t) (Term :- t)
    subGrammar =
      varargGrammar
        "-"
        Sub
        (\case
          Sub ts -> Right ts
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
          Xor t1 t2 -> Right [t1, t2]
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

    trinopGrammar ::
         Text
      -> (Term -> Term -> Term -> Term)
      -> (Term -> Either Mismatch (Term, (Term, Term)))
      -> Grammar Position (Sexp :- t) (Term :- t)
    trinopGrammar s f p =
      list (el (sym s) >>> el termGrammar >>> el termGrammar >>> el termGrammar) >>>
      pair >>>
      pair >>>
      partialIso
        (\(t1, (t2, t3)) -> f t1 t2 t3)
        p

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

compileTerm ::
     forall m sig.
     ( Carrier sig m
     , Member Z3 sig
     , Member Zzz sig
     )
  => Term
  -> m Z3.AST
compileTerm = \case
  Add ts ->
    wrapN ts Z3.mkAdd

  And ts ->
    wrapN ts Z3.mkAnd

  Apply f ts -> do
    decl <- getFunction f
    as <- traverse compileTerm ts
    Z3.mkApp decl as

  Distinct ts ->
    wrapN ts Z3.mkDistinct

  Eq t1 t2 ->
    wrap2 t1 t2 Z3.mkEq

  Ge t1 t2 ->
    wrap2 t1 t2 Z3.mkGe

  Gt t1 t2 ->
    wrap2 t1 t2 Z3.mkGt

  Iff t1 t2 ->
    wrap2 t1 t2 Z3.mkIff

  Implies t1 t2 ->
    wrap2 t1 t2 Z3.mkImplies

  Ite t1 t2 t3 ->
    wrap3 t1 t2 t3 Z3.mkIte

  Lit lit ->
    compileLit lit

  Le t1 t2 ->
    wrap2 t1 t2 Z3.mkLe

  Lt t1 t2 ->
    wrap2 t1 t2 Z3.mkLt

  Negate t ->
    wrap1 t Z3.mkUnaryMinus

  Not t ->
    wrap1 t Z3.mkNot

  Mul ts ->
    wrapN ts Z3.mkMul

  Or ts ->
    wrapN ts Z3.mkOr

  Sub ts ->
    wrapN ts Z3.mkSub

  Var var ->
    getVar var

  Xor t1 t2 ->
    wrap2 t1 t2 Z3.mkXor

  where
    wrap1 ::
         Term
      -> (Z3.AST -> m a)
      -> m a
    wrap1 t f =
      compileTerm t >>= f

    wrap2 ::
         Term
      -> Term
      -> (Z3.AST -> Z3.AST -> m a)
      -> m a
    wrap2 t1 t2 f = do
      a1 <- compileTerm t1
      a2 <- compileTerm t2
      f a1 a2

    wrap3 ::
         Term
      -> Term
      -> Term
      -> (Z3.AST -> Z3.AST -> Z3.AST -> m a)
      -> m a
    wrap3 t1 t2 t3 f = do
      a1 <- compileTerm t1
      a2 <- compileTerm t2
      a3 <- compileTerm t3
      f a1 a2 a3

    wrapN ::
         [Term]
      -> ([Z3.AST] -> m a)
      -> m a
    wrapN ts f =
      traverse compileTerm ts >>= f
