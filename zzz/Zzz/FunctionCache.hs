module Zzz.FunctionCache
  ( FunctionCache(..)
  , readFunctionCache
  ) where

import Cache (Cache, readCache)

import Control.Effect
import Control.Effect.Reader
import Control.Monad.IO.Class (MonadIO)
import Data.Text (Text)
import Z3.Effect (FuncDecl)


newtype FunctionCache
  = FunctionCache (Cache Text FuncDecl)

readFunctionCache ::
     ( Carrier sig m
     , Member (Reader FunctionCache) sig
     , MonadIO m
     )
  => Text
  -> m FuncDecl
readFunctionCache name = do
  FunctionCache cache <- ask

  readCache cache name >>= \case
    Nothing ->
      undefined

    Just decl ->
      pure decl
