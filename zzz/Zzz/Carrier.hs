{-# LANGUAGE UndecidableInstances #-}

module Zzz.Carrier
  ( ZzzC
  , runZzz
  ) where

import Framed (Framed, modifyFramed, newFramed)
import Zzz.Effect (Zzz(..))
import Zzz.Prelude
import Zzz.Syntax.Function (Function)
import Zzz.Syntax.Lit (Lit(..), compileLit)
import Zzz.Syntax.Sort (Sort(..), compileSort)
import Zzz.Syntax.Term (Term, compileTerm)
import Zzz.Syntax.Var (Var)

import qualified Zzz.Syntax.Term as Term
import qualified Zzz.Syntax.Var as Var

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Reader
import Control.Effect.Sum
import Control.Monad.IO.Class (MonadIO(..))
import Data.HashMap.Strict (HashMap)
import Data.Text (Text)
import Z3.Effect (Z3, Z3C)

import qualified Data.Text as Text
import qualified Data.HashMap.Strict as HashMap
import qualified Z3.Effect as Z3


-- TODO symbol cache

newtype ZzzC m a
  = ZzzC { unZzzC :: ReaderC Env m a }
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
      handleAssert term
      next

    L (Declare name sort next) ->
      ZzzC (handleDeclare name sort) >>= next

    R other ->
      ZzzC (eff (R (handleCoercible other)))

data Env
  = Env
  { envScopes :: IORef (Framed Scopes)
  }

newEnv :: MonadIO m => m Env
newEnv =
  Env
    <$> liftIO (newIORef (newFramed emptyScopes))

data Scopes
  = Scopes
  { funcScope :: HashMap Function Z3.FuncDecl
  , varScope :: HashMap Var Z3.AST
  }

emptyScopes :: Scopes
emptyScopes =
  Scopes HashMap.empty HashMap.empty


runZzz ::
     MonadIO m
  => ZzzC (Z3C m) a
  -> m a
runZzz action = do
  env <- newEnv
  Z3.runZ3 (runReader env (unZzzC action))


--------------------------------------------------------------------------------
-- Zzz handlers
--------------------------------------------------------------------------------

handleAssert ::
     ( Carrier sig m
     , Member Z3 sig
     , MonadIO m
     )
  => Term
  -> ZzzC m ()
handleAssert =
  compileTerm >=> Z3.solverAssertCnstr

handleDeclare ::
     ( Carrier sig m
     , Member Z3 sig
     , MonadIO m
     )
  => Text
  -> Sort
  -> ReaderC Env m Term
handleDeclare name sort = do
  symbol <- Z3.mkStringSymbol (Text.unpack name)
  sort' <- compileSort sort
  decl <- Z3.mkFuncDecl symbol [] sort'
  ast <- Z3.mkApp decl []
  let var = Var.Var name

  do
    let
      f :: Scopes -> Scopes
      f scopes =
        scopes { varScope = HashMap.insert var ast (varScope scopes) }

    Env scopesRef <- ask
    liftIO (modifyIORef' scopesRef (modifyFramed f))

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
