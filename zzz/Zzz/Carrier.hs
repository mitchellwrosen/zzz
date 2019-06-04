{-# LANGUAGE UndecidableInstances #-}

module Zzz.Carrier where

import Cache (Cache)
import Framed (Framed)
import Lit (Lit(..), compileLit)
import Sort (Sort(..), compileSort)
import Term (Term(..), compileTerm)
import Var (Var(..))
import Zzz.Effect (Zzz(..))
import Zzz.FunctionCache (FunctionCache)
import Zzz.VarCache (VarCache, writeVarCache)

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Sum
import Control.Monad ((>=>))
import Control.Monad.IO.Class (MonadIO)
import Data.HashMap.Strict (HashMap)
import Data.IORef
import Data.Text (Text)
import Z3.Effect (AST, FuncDecl, Z3, Z3C)

import qualified Data.Text as Text
import qualified Z3.Effect as Z3


newtype ZzzC m a
  = ZzzC { unZzzC :: ReaderC FunctionCache (ReaderC VarCache m) a }
  deriving newtype (Applicative, Functor, Monad)

instance
     ( Carrier sig m
     , Member Z3 sig
     , MonadIO m
     )
  => Carrier (Zzz :+: sig) (ZzzC m) where

  eff :: forall a. (Zzz :+: sig) (ZzzC m) (ZzzC m a) -> ZzzC m a
  eff = \case
    L (Assert term next) -> do
      ZzzC (handleAssert term)
      next

    L (Declare name sort next) ->
      ZzzC (handleDeclare name sort) >>= next

    R other ->
      undefined

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
     , Member (Reader FunctionCache) sig
     , Member (Reader VarCache) sig
     , Member Z3 sig
     , MonadIO m
     )
  => Term
  -> m ()
handleAssert =
  compileTerm >=> Z3.solverAssertCnstr

handleDeclare ::
     ( Carrier sig m
     , Member (Reader VarCache) sig
     , Member Z3 sig
     , MonadIO m
     )
  => Text
  -> Sort
  -> m Term
handleDeclare name sort = do
  symbol <- Z3.mkStringSymbol (Text.unpack name)
  sort' <- compileSort sort
  decl <- Z3.mkFuncDecl symbol [] sort'
  ast <- Z3.mkApp decl []
  writeVarCache name ast
  pure (Term.Var (Var.Var name))

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
