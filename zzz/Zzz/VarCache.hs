module Zzz.VarCache
  ( VarCache(..)
  , writeVarCache
  ) where

import Cache (Cache, writeCache)

import Control.Effect
import Control.Effect.Reader
import Control.Monad.IO.Class (MonadIO)
import Data.Text (Text)
import Z3.Effect (AST)


newtype VarCache
  = VarCache (Cache Text AST)

writeVarCache ::
     ( Carrier sig m
     , Member (Reader VarCache) sig
     , MonadIO m
     )
  => Text
  -> AST
  -> m ()
writeVarCache name ast = do
  VarCache cache <- ask
  writeCache cache name ast
