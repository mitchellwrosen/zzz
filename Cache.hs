module Cache
  ( Cache
  , newCache
  , pushCache
  , popCache
  , readCache
  , writeCache
  ) where

import Framed

import Control.Monad.IO.Class (MonadIO(..))
import Data.Hashable (Hashable)
import Data.HashMap.Strict (HashMap)
import Data.IORef

import qualified Data.HashMap.Strict as HashMap


newtype Cache k v =
  Cache (IORef (Framed (HashMap k v)))

newCache :: MonadIO m => m (Cache k v)
newCache = do
  liftIO (Cache <$> newIORef (newFramed HashMap.empty))

pushCache :: MonadIO m => Cache k v -> m ()
pushCache (Cache ref) =
  liftIO (modifyIORef' ref (pushFrame HashMap.empty))

popCache :: MonadIO m => Cache k v -> m ()
popCache (Cache ref) =
  liftIO (modifyIORef' ref popFrame)

readCache :: (Eq k, Hashable k, MonadIO m) => Cache k v -> k -> m (Maybe v)
readCache (Cache ref) k = do
  cache <-
    foldlFramed HashMap.union HashMap.empty <$>
      liftIO (readIORef ref)
  pure (HashMap.lookup k cache)

writeCache :: (Eq k, Hashable k, MonadIO m) => Cache k v -> k -> v -> m ()
writeCache (Cache ref) k v =
  liftIO (modifyIORef' ref (modifyFramed (HashMap.insert k v)))
