{-# LANGUAGE UndecidableInstances #-}

module Zzz
  ( Z3
  , Z3C
  , runZ3
    -- * Symbols
  , mkIntSymbol
  ) where

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Reader (ReaderC(..), runReader)
import Control.Effect.Sum
import Control.Monad.IO.Class (MonadIO(..))
import Data.Foldable (for_)
import Data.Kind (Type)
import Data.Text (Text, unpack)
import Data.Word
import Z3.Base (Context, Symbol)

import qualified Z3.Base as Z3


data Z3 (m :: Type -> Type) (k :: Type) where
  MkIntSymbol ::
       Word32
    -> (Symbol -> k)

    -> Z3 m k
  deriving stock (Functor)
  deriving anyclass (HFunctor)

newtype Z3C (m :: Type -> Type) (a :: Type)
  = Z3C { unZ3C :: ReaderC Context m a }
  deriving newtype (Applicative, Functor, Monad, MonadIO)

instance (Carrier sig m, MonadIO m) => Carrier (Z3 :+: sig) (Z3C m) where
  eff :: (Z3 :+: sig) (Z3C m) (Z3C m a) -> Z3C m a
  eff = \case
    L z3 ->
      Z3C (ReaderC (\ctx -> handleZ3 ctx z3 >>= runReader ctx . unZ3C))

    R other ->
      Z3C (eff (R (handleCoercible other)))

handleZ3 :: MonadIO m => Context -> Z3 (Z3C m) x -> m x
handleZ3 ctx = \case
  MkIntSymbol n k ->
    k <$> liftIO (Z3.mkIntSymbol ctx n)

runZ3 ::
     MonadIO m
  => [(Text, Text)] -- ^ Config
  -> Z3C m a
  -> m a
runZ3 params action = do
  context :: Context <-
    liftIO $
      Z3.withConfig $ \config -> do
        for_ params $ \(k, v) ->
          Z3.setParamValue config (unpack k) (unpack v)
        Z3.mkContext config

  runReaderC (unZ3C action) context


--------------------------------------------------------------------------------
-- Symbols
--------------------------------------------------------------------------------

mkIntSymbol ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Word32
  -> m Symbol
mkIntSymbol n =
  send (MkIntSymbol n pure)
