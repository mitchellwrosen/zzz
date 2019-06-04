-- | Mutually recursive types.

module Zzz.Types where

import Zzz.Syntax.Function (Function)
import Zzz.Syntax.Lit (Lit(..))
import Zzz.Syntax.Sort (Sort)
import Zzz.Syntax.Var (Var)

import Control.Effect.Carrier (HFunctor)
import Data.Kind (Type)
import Data.Text (Text)

import qualified Z3.Effect as Z3


data Zzz (m :: Type -> Type) (k :: Type)
  = Assert Term k
  | Declare Text Sort (Term -> k)
  | GetFunction Function (Z3.FuncDecl -> k)
  | GetVar Var (Z3.AST -> k)
  deriving stock (Functor)
  deriving anyclass (HFunctor)

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
  | Store Term Term Term
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
    Ite (Ge e 0) e (Negate e)

  fromInteger =
    Lit . LitInt

  negate =
    Negate

  signum e =
    Ite (Gt e 0) 1 0

  t1 + t2 =
    Add [t1, t2]

  t1 * t2 =
    Mul [t1, t2]

  t1 - t2 =
    Sub [t1, t2]
