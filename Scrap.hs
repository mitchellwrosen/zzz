{-# LANGUAGE OverloadedStrings #-}

module Scrap where

import Control.Effect (runM)
import Control.Monad.IO.Class
import Zzz


scrap :: IO ()
scrap = do
  runM $ runZ3 [] $ do
    a <- mkBoolVar "a"
    b <- mkBoolVar "b"
    c <- mkBoolVar "c"
    assert (a =. true ||. b =. true &&. c =. true)
    check >>= liftIO . print
    getModel >>= printModel
