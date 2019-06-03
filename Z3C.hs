{-# LANGUAGE UndecidableInstances #-}

module Z3C
  ( Z3C(..)
  , runZ3
  ) where

import Framed
import Z3 (Z3(..))

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Reader (ReaderC(..), runReader)
import Control.Effect.Sum
import Control.Monad.IO.Class (MonadIO(..))
import Data.HashMap.Strict (HashMap)
import Data.IORef
import Data.Kind (Type)
import Data.Text (Text, pack, unpack)

import qualified Data.HashMap.Strict as HashMap
import qualified Z3.Base as Z3


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
  { z3cContext :: Z3.Context
  , z3cSolver :: Z3.Solver
  -- , z3cSymbolCache :: IORef (HashMap Text Z3.Symbol)
  , z3cFunctionCache :: IORef (Framed (HashMap Text Z3.FuncDecl))
  , z3cVarCache :: IORef (Framed (HashMap Text Z3.AST))
  }

handleZ3 :: MonadIO m => Z3CEnv -> Z3 (Z3C m) x -> m x
handleZ3 env@(Z3CEnv ctx solver functionCacheRef varCacheRef) = \case
  AstToString ast k ->
    k <$> liftIO (Z3.astToString ctx ast)

  Frame action k ->
    let
      inframe =
        liftIO do
          modifyIORef' functionCacheRef (pushFrame HashMap.empty)
          Z3.solverPush ctx solver

      outframe =
        liftIO do
          Z3.solverPop ctx solver 1
          modifyIORef' functionCacheRef popFrame
    in
      inframe
        *>
      (k <$> runReader env (unZ3C action))
        <*
      outframe

  MkAdd as k ->
    vararg as k Z3.mkAdd

  MkAnd as k ->
    vararg as k Z3.mkAnd

  MkApp decl args k ->
    k <$> liftIO (Z3.mkApp ctx decl args)

  MkBoolSort k ->
    nullary k Z3.mkBoolSort

  MkDistinct as k ->
    vararg as k Z3.mkDistinct

  MkEq a1 a2 k ->
    binop a1 a2 k Z3.mkEq

  MkFalse k ->
    nullary k Z3.mkFalse

  MkFuncDecl name args sort k ->
    k <$> liftIO (Z3.mkFuncDecl ctx name args sort)

  MkGe a1 a2 k ->
    binop a1 a2 k Z3.mkGe

  MkGt a1 a2 k ->
    binop a1 a2 k Z3.mkGt

  MkIff a1 a2 k ->
    binop a1 a2 k Z3.mkIff

  MkImplies a1 a2 k ->
    binop a1 a2 k Z3.mkImplies

  MkIntSort k ->
    nullary k Z3.mkIntSort

  MkInteger n k ->
    k <$> liftIO (Z3.mkInteger ctx n)

  MkIntSymbol n k ->
    k <$> liftIO (Z3.mkIntSymbol ctx n)

  MkIte a1 a2 a3 k ->
    k <$> liftIO (Z3.mkIte ctx a1 a2 a3)

  MkLe a1 a2 k ->
    binop a1 a2 k Z3.mkLe

  MkLt a1 a2 k ->
    binop a1 a2 k Z3.mkLt

  MkMul as k ->
    vararg as k Z3.mkMul

  MkNot a k ->
    unop a k Z3.mkNot

  MkOr as k ->
    vararg as k Z3.mkOr

  MkSolver k ->
    nullary k Z3.mkSolver

  MkStringSymbol s k ->
    k <$> liftIO (Z3.mkStringSymbol ctx (unpack s))

  MkSub as k ->
    vararg as k Z3.mkSub

  MkTrue k ->
    nullary k Z3.mkTrue

  MkUnaryMinus a k ->
    unop a k Z3.mkUnaryMinus

  MkXor a1 a2 k ->
    binop a1 a2 k Z3.mkXor

  ModelToString model k ->
    k . pack <$> liftIO (Z3.modelToString ctx model)

  Simplify ast k ->
    k <$> liftIO (Z3.simplify ctx ast)

  SolverAssertCnstr ast k ->
    k <$ liftIO (Z3.solverAssertCnstr ctx solver ast)

  SolverCheck k ->
    k <$> liftIO (Z3.solverCheck ctx solver)

  SolverGetModel k ->
    k <$> liftIO (Z3.solverGetModel ctx solver)

  ReadFunctionCache name k -> do
    cache <-
      foldlFramed HashMap.union HashMap.empty <$>
        liftIO (readIORef functionCacheRef)

    case HashMap.lookup name cache of
      Nothing ->
        error $ "Undefined function: " ++ unpack name

      Just decl ->
        pure (k decl)

  ReadVarCache var k -> do
    cache <-
      foldlFramed HashMap.union HashMap.empty <$>
        liftIO (readIORef varCacheRef)

    case HashMap.lookup var cache of
      Nothing ->
        error $ "Undefined var: " ++ show var

      Just ast ->
        pure (k ast)

  WriteFunctionCache name decl k -> do
    liftIO
      (modifyIORef'
        functionCacheRef
        (modifyFramed (HashMap.insert name decl)))
    pure k

  WriteVarCache var ast k -> do
    liftIO
      (modifyIORef'
        varCacheRef
        (modifyFramed (HashMap.insert var ast)))
    pure k

  where
    unop a k f =
      k <$> liftIO (f ctx a)

    binop a1 a2 k f =
      k <$> liftIO (f ctx a1 a2)

    nullary :: MonadIO m => (a -> b) -> (Z3.Context -> IO a) -> m b
    nullary k f =
      k <$> liftIO (f ctx)

    vararg as k f =
      k <$> liftIO (f ctx as)


runZ3 ::
     MonadIO m
  => Z3C m a
  -> m a
runZ3 action = do
  ctx :: Z3.Context <-
    liftIO (Z3.withConfig Z3.mkContext)

  solver :: Z3.Solver <-
    liftIO (Z3.mkSolver ctx)

  functionCache :: IORef (Framed (HashMap Text Z3.FuncDecl)) <-
    liftIO (newIORef (newFramed HashMap.empty))

  varCache :: IORef (Framed (HashMap Text Z3.AST)) <-
    liftIO (newIORef (newFramed HashMap.empty))

  -- symbolCache :: IORef (HashMap Text Z3.Symbol) <-
  --   liftIO (newIORef HashMap.empty)

  runReaderC (unZ3C action) Z3CEnv
    { z3cContext = ctx
    , z3cSolver = solver
    , z3cFunctionCache = functionCache
    , z3cVarCache = varCache
    -- , z3cSymbolCache = symbolCache
    }
