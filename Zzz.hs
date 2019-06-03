module Zzz
  ( Z3
  , Z3C
  , runZ3
    -- * Solver
  , assert
  , frame
  , check
  , getModel
  , printModel
  , modelToString
    -- * Simplifier
  , Zzz.simplify
    -- * Declarations
  , declare
  , declareFunction
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
  , Term.negate
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
import Lit
import Sort
import Term
import Var
import Z3
import Z3C

import Control.Category ((>>>))
import Control.Effect
import Control.Monad ((>=>))
import Control.Monad.IO.Class (MonadIO(..))
import Data.Foldable (traverse_)
import Data.Text (Text)

import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import qualified Z3.Base


printModel ::
     ( Carrier sig m
     , Member Z3 sig
     , MonadIO m
     )
  => Z3.Base.Model
  -> m ()
printModel model = do
  string <- modelToString model
  traverse_ (Text.putStrLn >>> liftIO) (Text.lines string)

declare ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Text
  -> Sort
  -> m Term
declare name sort = do
  symbol <- mkStringSymbol name
  sort' <- compileSort sort
  decl <- mkFuncDecl symbol [] sort'
  ast <- mkApp decl []
  writeVarCache name ast
  pure (Term.Var (Var.Var name))

declareFunction ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Text
  -> [Sort]
  -> Sort
  -> m Function
declareFunction name args sort = do
  symbol <- mkStringSymbol name
  args' <- traverse compileSort args
  sort' <- compileSort sort
  decl <- mkFuncDecl symbol args' sort'
  writeFunctionCache name decl
  pure (Function name)

compileLit ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Lit
  -> m Z3.Base.AST
compileLit = \case
  LitBool b ->
    if b then mkTrue else mkFalse

  LitInt n ->
    mkInteger n

compileSort ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Sort
  -> m Z3.Base.Sort
compileSort = \case
  SortBool ->
    mkBoolSort

  SortInt ->
    mkIntSort

compileTerm ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Term
  -> m Z3.Base.AST
compileTerm = \case
  Add es ->
    vararg es mkAdd

  And es ->
    vararg es mkAnd

  Apply f es -> do
    decl <- readFunctionCache (unFunction f)
    as <- traverse compileTerm es
    mkApp decl as

  Distinct es ->
    vararg es mkDistinct

  Eq e1 e2 ->
    binop e1 e2 mkEq

  Ge e1 e2 ->
    binop e1 e2 mkGe

  Gt e1 e2 ->
    binop e1 e2 mkGt

  Iff e1 e2 ->
    binop e1 e2 mkIff

  Implies e1 e2 ->
    binop e1 e2 mkImplies

  Ite e1 e2 e3 ->
    trinop e1 e2 e3 mkIte

  Lit lit ->
    compileLit lit

  Le e1 e2 ->
    binop e1 e2 mkLe

  Lt e1 e2 ->
    binop e1 e2 mkLt

  Negate e ->
    unop e mkUnaryMinus

  Not e ->
    unop e mkNot

  Mul es ->
    vararg es mkMul

  Or es ->
    vararg es mkOr

  Sub es ->
    vararg es mkSub

  Term.Var var ->
    readVarCache (unVar var)

  Xor e1 e2 ->
    binop e1 e2 mkXor

  where
    unop e f =
      compileTerm e >>= f

    binop e1 e2 f = do
      a1 <- compileTerm e1
      a2 <- compileTerm e2
      f a1 a2

    trinop e1 e2 e3 f = do
      a1 <- compileTerm e1
      a2 <- compileTerm e2
      a3 <- compileTerm e3
      f a1 a2 a3

    vararg es f =
      traverse compileTerm es >>= f

assert ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Term
  -> m ()
assert =
  compileTerm >=> solverAssertCnstr

simplify ::
     ( Carrier sig m
     , Member Z3 sig
     , MonadIO m
     )
  => Term
  -> m Term
simplify term = do
  ast <- compileTerm term
  ast' <- Z3.simplify ast
  astToString ast' >>= liftIO . putStrLn
  pure term
