module Zzz.Effect
  ( Zzz(..)
  , assert
  , declare
  ) where

import Sort (Sort)
import Term (Term)

import Control.Effect
import Control.Effect.Carrier
import Data.Kind (Type)
import Data.Text (Text)


data Zzz (m :: Type -> Type) (k :: Type)
  = Assert Term k
  | Declare Text Sort (Term -> k)
  deriving stock (Functor)
  deriving anyclass (HFunctor)

assert ::
     ( Carrier sig m
     , Member Zzz sig
     )
  => Term
  -> m ()
assert term =
  send (Assert term (pure ()))

declare ::
     ( Carrier sig m
     , Member Zzz sig
     )
  => Text
  -> Sort
  -> m Term
declare name sort =
  send (Declare name sort pure)

-- declareFunction ::
--      ( Carrier sig m
--      , Member Z3 sig
--      , Member Zzz sig
--      )
--   => Text
--   -> [Sort]
--   -> Sort
--   -> m Function
-- declareFunction name args sort = do
--   symbol <- Z3.mkStringSymbol name
--   args' <- traverse compileSort args
--   sort' <- compileSort sort
--   decl <- Z3.mkFuncDecl symbol args' sort'
--   writeFunctionCache name decl
--   pure (Function name)

-- compileLit ::
--      ( Carrier sig m
--      , Member Z3 sig
--      )
--   => Lit
--   -> m Z3.Base.AST
-- compileLit = \case
--   LitBool b ->
--     if b then Z3.mkTrue else Z3.mkFalse

--   LitInt n ->
--     Z3.mkInteger n

-- compileTerm ::
--      ( Carrier sig m
--      , Member Z3 sig
--      , Member Zzz sig
--      )
--   => Term
--   -> m Z3.Base.AST
-- compileTerm = \case
--   Add es ->
--     vararg es Z3.mkAdd

--   And es ->
--     vararg es Z3.mkAnd

--   Apply f es -> do
--     decl <- readFunctionCache (unFunction f)
--     as <- traverse compileTerm es
--     Z3.mkApp decl as

--   Distinct es ->
--     vararg es Z3.mkDistinct

--   Eq e1 e2 ->
--     binop e1 e2 Z3.mkEq

--   Ge e1 e2 ->
--     binop e1 e2 Z3.mkGe

--   Gt e1 e2 ->
--     binop e1 e2 Z3.mkGt

--   Iff e1 e2 ->
--     binop e1 e2 Z3.mkIff

--   Implies e1 e2 ->
--     binop e1 e2 Z3.mkImplies

--   Ite e1 e2 e3 ->
--     trinop e1 e2 e3 Z3.mkIte

--   Lit lit ->
--     compileLit lit

--   Le e1 e2 ->
--     binop e1 e2 Z3.mkLe

--   Lt e1 e2 ->
--     binop e1 e2 Z3.mkLt

--   Negate e ->
--     unop e Z3.mkUnaryMinus

--   Not e ->
--     unop e Z3.mkNot

--   Mul es ->
--     vararg es Z3.mkMul

--   Or es ->
--     vararg es Z3.mkOr

--   Sub es ->
--     vararg es Z3.mkSub

--   Term.Var var ->
--     readVarCache (unVar var)

--   Xor e1 e2 ->
--     binop e1 e2 Z3.mkXor

--   where
--     unop e f =
--       compileTerm e >>= f

--     binop e1 e2 f = do
--       a1 <- compileTerm e1
--       a2 <- compileTerm e2
--       f a1 a2

--     trinop e1 e2 e3 f = do
--       a1 <- compileTerm e1
--       a2 <- compileTerm e2
--       a3 <- compileTerm e3
--       f a1 a2 a3

--     vararg es f =
--       traverse compileTerm es >>= f

-- assert ::
--      ( Carrier sig m
--      , Member Z3 sig
--      , Member Zzz sig
--      )
--   => Term
--   -> m ()
-- assert =
--   compileTerm >=> Z3.solverAssertCnstr

-- simplify ::
--      ( Carrier sig m
--      , Member Z3 sig
--      , Member Zzz sig
--      , MonadIO m
--      )
--   => Term
--   -> m Term
-- simplify term = do
--   ast <- compileTerm term
--   ast' <- Z3.simplify ast
--   str <- Z3.astToString ast'
--   case parseTerm str of
--     Left err -> error ("parseTerm: " ++ err)
--     Right term' -> pure term'
