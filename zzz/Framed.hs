module Framed where

import Data.List (foldl')


-- | Stack frames, where the base frame always exists.
--
-- @
-- Framed 0 [4,3,2,1]
-- @
data Framed a
  = Framed a [a]

newFramed :: a -> Framed a
newFramed x =
  Framed x []

pushFrame :: a -> Framed a -> Framed a
pushFrame y (Framed x xs) =
  Framed x (y:xs)

popFrame :: Framed a -> Framed a
popFrame (Framed x xs) =
  Framed x (drop 1 xs)

-- | Fold a 'Framed' with the top stack frame on the left, as in
--
-- @
-- n <> n-1 <> ... <> 0 <> mempty
-- @
foldFramed :: Monoid a => Framed a -> a
foldFramed (Framed x xs) =
  foldl' (<>) mempty xs <> x

modifyFramed :: (a -> a) -> Framed a -> Framed a
modifyFramed f = \case
  Framed x [] -> Framed (f x) []
  Framed x (y:ys) -> Framed x (f y : ys)

