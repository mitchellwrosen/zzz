module Zzz.Prelude
  ( module X
  ) where

import Control.Category as X ((>>>))
import Control.Monad as X ((>=>))
import Control.Monad.IO.Class as X (MonadIO(..))
import Data.Foldable as X (traverse_)
import Data.Function as X ((&))
import Data.IORef as X
import Data.Kind as X (Type)
import GHC.Generics as X (Generic)
import Prelude as X
