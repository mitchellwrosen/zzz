{-# LANGUAGE OverloadedStrings #-}

module Scrap where

import Control.Effect (runM)
import Zzz

scrap :: IO ()
scrap = do
  result <-
    runM $ runZ3 [] $ do
      a <- mkBoolVar "a"
      assert (Eq (Var a) (Lit True))
      check
  print result
