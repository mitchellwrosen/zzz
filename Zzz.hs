{-# LANGUAGE UndecidableInstances #-}

module Zzz
  ( Z3
  , Z3C
  , runZ3
    -- * Variables
  , mkBoolVar
    -- * Assertions
  , assert
  , Expr(..)
  , Var
    -- * Solver
  , check
  ) where

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Reader (ReaderC(..), runReader)
import Control.Effect.Sum
import Control.Monad (void)
import Control.Monad.IO.Class (MonadIO(..))
import Data.Foldable (for_)
import Data.IORef
import Data.HashMap.Strict (HashMap)
import Data.Kind (Type)
import Data.Text (Text, unpack)
import Data.Word
import Z3.Base (Context)

import qualified Data.HashMap.Strict as HashMap
import qualified Z3.Base as Z3


data Z3 (m :: Type -> Type) (k :: Type) where
  MkAdd ::
       [Z3.AST]
    -> (Z3.AST -> k)
    -> Z3 m k

  MkAnd ::
       [Z3.AST]
    -> (Z3.AST -> k)
    -> Z3 m k

  MkBoolSort ::
       (Z3.Sort -> k)
    -> Z3 m k

  MkConst ::
       Z3.Symbol
    -> Z3.Sort
    -> (Z3.AST -> k)
    -> Z3 m k

  MkEq ::
       Z3.AST
    -> Z3.AST
    -> (Z3.AST -> k)
    -> Z3 m k

  MkFalse ::
       (Z3.AST -> k)
    -> Z3 m k

  MkDistinct ::
       [Z3.AST]
    -> (Z3.AST -> k)
    -> Z3 m k

  MkIntSymbol ::
       Word32
    -> (Z3.Symbol -> k)
    -> Z3 m k

  MkSolver ::
       (Z3.Solver -> k)
    -> Z3 m k

  MkStringSymbol ::
       Text
    -> (Z3.Symbol -> k)
    -> Z3 m k

  MkTrue ::
       (Z3.AST -> k)
    -> Z3 m k

  SolverAssertCnstr ::
       Z3.Solver
    -> Z3.AST
    -> k
    -> Z3 m k

  SolverCheck ::
       Z3.Solver
    -> (Z3.Result -> k)
    -> Z3 m k

  deriving stock (Functor)
  deriving anyclass (HFunctor)

newtype Z3C (m :: Type -> Type) (a :: Type)
  = Z3C { unZ3C :: ReaderC Z3CEnv m a }
  deriving newtype (Applicative, Functor, Monad, MonadIO)

instance (Carrier sig m, MonadIO m) => Carrier (Z3 :+: sig) (Z3C m) where
  eff :: (Z3 :+: sig) (Z3C m) (Z3C m a) -> Z3C m a
  eff = \case
    L z3 ->
      Z3C (ReaderC (\env -> handleZ3 env z3 >>= runReader env . unZ3C))

    R other ->
      Z3C (eff (R (handleCoercible other)))

data Z3CEnv
  = Z3CEnv
  { z3cContext :: Context
  , z3cSymbolCache :: IORef (HashMap Text Z3.Symbol)
  }

handleZ3 :: MonadIO m => Z3CEnv -> Z3 (Z3C m) x -> m x
handleZ3 (Z3CEnv ctx _symbolCache) = \case
  MkAdd asts k ->
    k <$> liftIO (Z3.mkAdd ctx asts)

  MkAnd asts k ->
    k <$> liftIO (Z3.mkAnd ctx asts)

  MkBoolSort k ->
    k <$> liftIO (Z3.mkBoolSort ctx)

  MkConst symbol sort k ->
    k <$> liftIO (Z3.mkConst ctx symbol sort)

  MkDistinct asts k ->
    k <$> liftIO (Z3.mkDistinct ctx asts)

  MkEq e1 e2 k ->
    k <$> liftIO (Z3.mkEq ctx e1 e2)

  MkFalse k ->
    k <$> liftIO (Z3.mkFalse ctx)

  MkIntSymbol n k ->
    k <$> liftIO (Z3.mkIntSymbol ctx n)

  MkSolver k ->
    k <$> liftIO (Z3.mkSolver ctx)

  MkStringSymbol s k ->
    k <$> liftIO (Z3.mkStringSymbol ctx (unpack s))

  MkTrue k ->
    k <$> liftIO (Z3.mkTrue ctx)

  SolverAssertCnstr solver ast k -> do
    liftIO (Z3.solverAssertCnstr ctx solver ast)
    pure k

  SolverCheck solver k -> do
    k <$> liftIO (Z3.solverCheck ctx solver)

runZ3 ::
     MonadIO m
  => [(Text, Text)] -- ^ Config
  -> Z3C m a
  -> m a
runZ3 params action = do
  ctx :: Context <-
    liftIO $
      Z3.withConfig $ \config -> do
        for_ params $ \(k, v) ->
          Z3.setParamValue config (unpack k) (unpack v)
        Z3.mkContext config

  symbolCache :: IORef (HashMap Text Z3.Symbol) <-
    liftIO (newIORef HashMap.empty)

  runReaderC (unZ3C action) Z3CEnv
    { z3cContext = ctx
    , z3cSymbolCache = symbolCache
    }


--------------------------------------------------------------------------------
-- Expression
-------------------------------------------------------------------------------

data Expr
  = Add [Expr]
  | And [Expr]
  | Distinct [Expr]
  | Eq Expr Expr
  | Iff Expr Expr
  | Implies Expr Expr
  | Ite Expr Expr Expr
  | Lit Bool
  | Mul [Expr]
  | Or [Expr]
  | Not Expr
  | Sub [Expr]
  | Var Var
  | Xor Expr Expr

newtype Var
  = MkVar { unVar :: Z3.AST }


assert ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Expr
  -> m ()
assert expr = do
  ast <- compile expr
  solver <- mkSolver
  solverAssertCnstr solver ast

compile ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Expr
  -> m Z3.AST
compile = \case
  Add es ->
    traverse compile es >>= mkAdd

  And es ->
    traverse compile es >>= mkAnd

  Distinct es ->
    traverse compile es >>= mkDistinct

  Eq e1 e2 -> do
    a1 <- compile e1
    a2 <- compile e2
    mkEq a1 a2

  Lit lit ->
    if lit then mkTrue else mkFalse

  Var var ->
    pure (unVar var)


--------------------------------------------------------------------------------
-- Solver
--------------------------------------------------------------------------------

check ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => m Z3.Result
check = do
  solver <- mkSolver
  send (SolverCheck solver pure)

--------------------------------------------------------------------------------
-- Z3 API
--------------------------------------------------------------------------------

mkAdd ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => [Z3.AST]
  -> m Z3.AST
mkAdd asts =
  send (MkAdd asts pure)

mkAnd ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => [Z3.AST]
  -> m Z3.AST
mkAnd asts =
  send (MkAnd asts pure)

mkBoolSort ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => m Z3.Sort
mkBoolSort =
  send (MkBoolSort pure)

mkBoolVar ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Text
  -> m Var
mkBoolVar name = do
  symbol <- mkStringSymbol name
  sort <- mkBoolSort
  MkVar <$> mkConst symbol sort

mkConst ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Z3.Symbol
  -> Z3.Sort
  -> m Z3.AST
mkConst symbol sort =
  send (MkConst symbol sort pure)

mkDistinct ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => [Z3.AST]
  -> m Z3.AST
mkDistinct asts =
  send (MkDistinct asts pure)

mkEq ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Z3.AST
  -> Z3.AST
  -> m Z3.AST
mkEq a1 a2 =
  send (MkEq a1 a2 pure)

mkFalse ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => m Z3.AST
mkFalse =
  send (MkFalse pure)

mkIntSymbol ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Word32
  -> m Z3.Symbol
mkIntSymbol n =
  send (MkIntSymbol n pure)

mkStringSymbol ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Text
  -> m Z3.Symbol
mkStringSymbol s =
  send (MkStringSymbol s pure)

mkSolver ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => m Z3.Solver
mkSolver =
  send (MkSolver pure)

mkTrue ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => m Z3.AST
mkTrue =
  send (MkTrue pure)

solverAssertCnstr ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Z3.Solver
  -> Z3.AST
  -> m ()
solverAssertCnstr solver ast =
  send (SolverAssertCnstr solver ast (pure ()))
