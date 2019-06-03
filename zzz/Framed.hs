module Framed where

import Data.List (foldl')


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

foldlFramed :: (b -> a -> b) -> b -> Framed a -> b
foldlFramed f z (Framed x xs) =
  f (foldl' f z xs) x

modifyFramed :: (a -> a) -> Framed a -> Framed a
modifyFramed f = \case
  Framed x [] -> Framed (f x) []
  Framed x (y:ys) -> Framed x (f y : ys)

