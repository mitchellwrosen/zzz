{-# LANGUAGE UndecidableInstances #-}

module Zzz.Carrier where

import Framed (Framed)
import Lit (Lit(..))
import Term (Term(..))
import Var (Var(..))
import Zzz.Effect (Zzz(..))

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Sum
import Control.Monad.IO.Class (MonadIO)
import Data.HashMap.Strict (HashMap)
import Data.IORef
import Data.Text (Text)
import Z3.Base (AST, FuncDecl)
import Z3.Effect (Z3, Z3C)

import qualified Z3.Effect as Z3


newtype ZzzC m a
  = ZzzC { unZzzC :: ReaderC Env m a }
  deriving newtype (Applicative, Functor, Monad)

instance
     ( Carrier sig m
     , Member Z3 sig
     )
  => Carrier (Zzz :+: sig) (ZzzC m) where

  eff :: (Zzz :+: sig) (ZzzC m) (ZzzC m a) -> ZzzC m a
  eff = \case
    L (Assert term next) -> do
      handleAssert term
      next

    R other ->
      undefined

data Env
  = Env

runZzz ::
     MonadIO m
  => ZzzC (Z3C m) a
  -> m a
runZzz =
  undefined


--------------------------------------------------------------------------------
-- Zzz handlers
--------------------------------------------------------------------------------

handleAssert ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Term
  -> m ()
handleAssert =
  undefined

  -- Frame action k ->
  --   let
  --     inframe =
  --       liftIO do
  --         modifyIORef' functionCacheRef (pushFrame HashMap.empty)
  --         Z3.solverPush ctx solver

  --     outframe =
  --       liftIO do
  --         Z3.solverPop ctx solver 1
  --         modifyIORef' functionCacheRef popFrame
  --   in
  --     inframe
  --       *>
  --     (k <$> runReader env (unZ3C action))
  --       <*
  --     outframe



--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

compileLit ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Lit
  -> m Z3.Base.AST

compileLit = \case
  LitBool b ->
    if b then Z3.mkTrue else Z3.mkFalse

  LitInt n ->
    Z3.mkInteger n
compileTerm ::
     ( Carrier sig m
     , Member (Reader (IORef (Framed (HashMap Text AST)))) sig
     , Member (Reader (IORef (Framed (HashMap Text FuncDecl)))) sig
     , Member Z3 sig
     )
  => Term
  -> m AST
compileTerm = \case
  Add es ->
    vararg es Z3.mkAdd

  And es ->
    vararg es Z3.mkAnd

  Apply f es -> do
    undefined
    -- decl <- readFunctionCache (unFunction f)
    -- as <- traverse compileTerm es
    -- Z3.mkApp decl as

  Distinct es ->
    vararg es Z3.mkDistinct

  Eq e1 e2 ->
    binop e1 e2 Z3.mkEq

  Ge e1 e2 ->
    binop e1 e2 Z3.mkGe

  Gt e1 e2 ->
    binop e1 e2 Z3.mkGt

  Iff e1 e2 ->
    binop e1 e2 Z3.mkIff

  Implies e1 e2 ->
    binop e1 e2 Z3.mkImplies

  Ite e1 e2 e3 ->
    trinop e1 e2 e3 Z3.mkIte

  Lit lit ->
    compileLit lit

  Le e1 e2 ->
    binop e1 e2 Z3.mkLe

  Lt e1 e2 ->
    binop e1 e2 Z3.mkLt

  Negate e ->
    unop e Z3.mkUnaryMinus

  Not e ->
    unop e Z3.mkNot

  Mul es ->
    vararg es Z3.mkMul

  Or es ->
    vararg es Z3.mkOr

  Sub es ->
    vararg es Z3.mkSub

  Term.Var var ->
    undefined
    -- readVarCache (unVar var)

  Xor e1 e2 ->
    binop e1 e2 Z3.mkXor

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
