module Term where

import Function (Function)
import Lit (Lit(..))

import Data.Text (Text)

import qualified Z3.Base as Z3


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
  | Lit Lit
  | Le Term Term
  | Lt Term Term
  | Negate Term
  | Mul [Term]
  | Or [Term]
  | Not Term
  | Sub [Term]
  | Var Text Z3.AST
  | Xor Term Term

  -- div
  -- mod
  -- rem
  -- int2real
  -- real2int
  -- isInt

instance Num Term where
  fromInteger =
    Lit . LitInt

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

negate :: Term -> Term
negate =
  Negate

apply :: Function -> [Term] -> Term
apply =
  Apply
