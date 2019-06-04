module Scrap where

import Control.Effect (runM)
import Control.Monad.IO.Class
import Zzz

-- Legal parameters are:
--   auto_config (bool) (default: true)
--   debug_ref_count (bool) (default: false)
--   dot_proof_file (string) (default: proof.dot)
--   dump_models (bool) (default: false)
--   model (bool) (default: true)
--   model_compress (bool) (default: true)
--   model_validate (bool) (default: false)
--   proof (bool) (default: false)
--   rlimit (unsigned int) (default: 0)
--   smtlib2_compliant (bool) (default: false)
--   stats (bool) (default: false)
--   timeout (unsigned int) (default: 4294967295)
--   trace (bool) (default: false)
--   trace_file_name (string) (default: z3.log)
--   type_check (bool) (default: true)
--   unsat_core (bool) (default: false)
--   well_sorted_check (bool) (default: false)

blep :: IO ()
blep =
  runM $ runZ3 do
    a <- declare "a" boolSort
    b <- declare "b" boolSort
    t <- simplify (xor a b)
    pure ()

scrap :: IO ()
scrap = do
  runM $ runZ3 do
    {-
        (declare-const a Int)
        (declare-fun f (Int Bool) Int)
        (assert (> a 10))
        (assert (< (f a true) 100))
        (check-sat)
        (get-model)
    -}
    a <- declare "a" intSort
    f <- declareFunction "f" [intSort, boolSort] intSort
    assert (a >. 10)
    assert (apply f [a, true] <. 100)
    check >>= liftIO . print
    getModel >>= printModel

  runM $ runZ3 $ do
    {-
        (declare-const x Int)
        (declare-const y Int)
        (declare-const z Int)
        (push)
        (assert (= (+ x y) 10))
        (assert (= (+ x (* 2 y)) 20))
        (check-sat)
        (pop) ; remove the two assertions
        (push)
        (assert (= (+ (* 3 x) y) 10))
        (assert (= (+ (* 2 x) (* 2 y)) 21))
        (check-sat)
        (declare-const p Bool)
        (pop)
        (assert p) ; error, since declaration of p was removed from the stack
    -}
    x <- declare "x" intSort
    y <- declare "y" intSort
    z <- declare "z" intSort
    frame do
      assert (x + y =. 10)
      assert (x + 2*y =. 20)
      check >>= liftIO . print
    p <-
      frame do
        assert (3*x + y =. 10)
        assert (2*x + 2*y =. 21)
        check >>= liftIO . print
        declare "p" boolSort
    assert p

    {-
        (declare-const a (Array Int Int))
        (declare-const x Int)
        (declare-const y Int)
        (simplify (+ x 2 x 1))
        (simplify (* (+ x y) (+ x y)))
        (simplify (= (store (store a 1 2) 4 3)
                    (store (store a 4 3) 1 2)))
        (help simplify)
    -}
    a <- declare "a" (arraySort intSort intSort)
    x <- declare "x" intSort
    y <- declare "y" intSort
    simplify (x + 2 + x + 1) >>= liftIO . print
    simplify ((x + y) * (x + y)) >>= liftIO . print
    simplify (store (store a 1 2) 4 3 =. store (store a 4 3) 1 2) >>= liftIO . print
