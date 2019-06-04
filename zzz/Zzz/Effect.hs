module Zzz.Effect
  ( Zzz(..)
  , assert
  , declare
  , getFunction
  , getVar
  ) where

import Zzz.Syntax.Function (Function)
import Zzz.Syntax.Sort (Sort)
import Zzz.Syntax.Var (Var)
import Zzz.Types (Term, Zzz(..))

import Control.Effect
import Control.Effect.Carrier
import Data.Kind (Type)
import Data.Text (Text)

import qualified Z3.Effect as Z3


assert ::
     ( Carrier sig m
     , Member Zzz sig
     )
  => Term
  -> m ()
assert term =
  send (Assert term (pure ()))

declare ::
     ( Carrier sig m
     , Member Zzz sig
     )
  => Text
  -> Sort
  -> m Term
declare name sort =
  send (Declare name sort pure)

-- declareFunction ::
--      ( Carrier sig m
--      , Member Z3 sig
--      , Member Zzz sig
--      )
--   => Text
--   -> [Sort]
--   -> Sort
--   -> m Function
-- declareFunction name args sort = do
--   symbol <- Z3.mkStringSymbol name
--   args' <- traverse compileSort args
--   sort' <- compileSort sort
--   decl <- Z3.mkFuncDecl symbol args' sort'
--   writeFunctionCache name decl
--   pure (Function name)

getFunction ::
     ( Carrier sig m
     , Member Zzz sig
     )
  => Function
  -> m Z3.FuncDecl
getFunction func =
  send (GetFunction func pure)

getVar ::
     ( Carrier sig m
     , Member Zzz sig
     )
  => Var
  -> m Z3.AST
getVar var =
  send (GetVar var pure)

-- simplify ::
--      ( Carrier sig m
--      , Member Z3 sig
--      , Member Zzz sig
--      , MonadIO m
--      )
--   => Term
--   -> m Term
-- simplify term = do
--   ast <- compileTerm term
--   ast' <- Z3.simplify ast
--   str <- Z3.astToString ast'
--   case parseTerm str of
--     Left err -> error ("parseTerm: " ++ err)
--     Right term' -> pure term'
