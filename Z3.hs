module Z3 where

import Function
import Lit
import Sort
import Term

import Control.Category ((>>>))
import Control.Effect
import Control.Effect.Carrier
import Control.Monad ((>=>))
import Control.Monad.IO.Class (MonadIO(..))
import Data.Foldable (traverse_)
import Data.Kind (Type)
import Data.Text (Text)
import Data.Word

import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import qualified Z3.Base as Z3


data Z3 (m :: Type -> Type) (k :: Type) where
  Frame ::
       m a
    -> (a -> k)
    -> Z3 m k

  MkAdd ::
       [Z3.AST]
    -> (Z3.AST -> k)
    -> Z3 m k

  MkAnd ::
       [Z3.AST]
    -> (Z3.AST -> k)
    -> Z3 m k

  MkApp ::
       Z3.FuncDecl
    -> [Z3.AST]
    -> (Z3.AST -> k)
    -> Z3 m k

  MkBoolSort ::
       (Z3.Sort -> k)
    -> Z3 m k

  MkDistinct ::
       [Z3.AST]
    -> (Z3.AST -> k)
    -> Z3 m k

  MkEq ::
       Z3.AST
    -> Z3.AST
    -> (Z3.AST -> k)
    -> Z3 m k

  MkFalse ::
       (Z3.AST -> k)
    -> Z3 m k

  MkFuncDecl ::
       Z3.Symbol
    -> [Z3.Sort]
    -> Z3.Sort
    -> (Z3.FuncDecl -> k)
    -> Z3 m k

  MkGe ::
       Z3.AST
    -> Z3.AST
    -> (Z3.AST -> k)
    -> Z3 m k

  MkGt ::
       Z3.AST
    -> Z3.AST
    -> (Z3.AST -> k)
    -> Z3 m k

  MkIff ::
       Z3.AST
    -> Z3.AST
    -> (Z3.AST -> k)
    -> Z3 m k

  MkImplies ::
       Z3.AST
    -> Z3.AST
    -> (Z3.AST -> k)
    -> Z3 m k

  MkInteger ::
       Integer
    -> (Z3.AST -> k)
    -> Z3 m k

  MkIntSort ::
       (Z3.Sort -> k)
    -> Z3 m k

  MkIntSymbol ::
       Word32
    -> (Z3.Symbol -> k)
    -> Z3 m k

  MkIte ::
       Z3.AST
    -> Z3.AST
    -> Z3.AST
    -> (Z3.AST -> k)
    -> Z3 m k

  MkLe ::
       Z3.AST
    -> Z3.AST
    -> (Z3.AST -> k)
    -> Z3 m k

  MkLt ::
       Z3.AST
    -> Z3.AST
    -> (Z3.AST -> k)
    -> Z3 m k

  MkMul ::
       [Z3.AST]
    -> (Z3.AST -> k)
    -> Z3 m k

  MkNot ::
       Z3.AST
    -> (Z3.AST -> k)
    -> Z3 m k

  MkOr ::
       [Z3.AST]
    -> (Z3.AST -> k)
    -> Z3 m k

  MkSolver ::
       (Z3.Solver -> k)
    -> Z3 m k

  MkStringSymbol ::
       Text
    -> (Z3.Symbol -> k)
    -> Z3 m k

  MkSub ::
       [Z3.AST]
    -> (Z3.AST -> k)
    -> Z3 m k

  MkTrue ::
       (Z3.AST -> k)
    -> Z3 m k

  MkUnaryMinus ::
       Z3.AST
    -> (Z3.AST -> k)
    -> Z3 m k

  MkXor ::
       Z3.AST
    -> Z3.AST
    -> (Z3.AST -> k)
    -> Z3 m k

  ModelToString ::
       Z3.Model
    -> (Text -> k)
    -> Z3 m k

  SolverAssertCnstr ::
       Z3.AST
    -> k
    -> Z3 m k

  SolverCheck ::
       (Z3.Result -> k)
    -> Z3 m k

  SolverGetModel ::
       (Z3.Model -> k)
    -> Z3 m k

  ReadFunctionCache ::
       Function
    -> (Z3.FuncDecl -> k)
    -> Z3 m k

  WriteFunctionCache ::
       Function
    -> Z3.FuncDecl
    -> k
    -> Z3 m k

deriving instance Functor (Z3 m)

instance HFunctor Z3 where
  hmap :: (forall x. m x -> n x) -> Z3 m a -> Z3 n a
  hmap f = \case
    Frame a b -> Frame (f a) b
    MkAdd a b -> MkAdd a b
    MkAnd a b -> MkAnd a b
    MkApp a b c -> MkApp a b c
    MkBoolSort a -> MkBoolSort a
    MkDistinct a b -> MkDistinct a b
    MkEq a b c -> MkEq a b c
    MkFalse a -> MkFalse a
    MkFuncDecl a b c d -> MkFuncDecl a b c d
    MkGe a b c -> MkGe a b c
    MkGt a b c -> MkGt a b c
    MkIff a b c -> MkIff a b c
    MkImplies a b c -> MkImplies a b c
    MkInteger a b -> MkInteger a b
    MkIntSort a -> MkIntSort a
    MkIntSymbol a b -> MkIntSymbol a b
    MkIte a b c d -> MkIte a b c d
    MkLe a b c -> MkLe a b c
    MkLt a b c -> MkLt a b c
    MkMul a b -> MkMul a b
    MkNot a b -> MkNot a b
    MkOr a b -> MkOr a b
    MkSolver a -> MkSolver a
    MkStringSymbol a b -> MkStringSymbol a b
    MkSub a b -> MkSub a b
    MkTrue a -> MkTrue a
    MkUnaryMinus a b -> MkUnaryMinus a b
    MkXor a b c -> MkXor a b c
    ModelToString a b -> ModelToString a b
    SolverAssertCnstr a b -> SolverAssertCnstr a b
    SolverCheck a -> SolverCheck a
    SolverGetModel a -> SolverGetModel a

    ReadFunctionCache a b -> ReadFunctionCache a b
    WriteFunctionCache a b c -> WriteFunctionCache a b c


--------------------------------------------------------------------------------
-- Declarations
-------------------------------------------------------------------------------

declare ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Text
  -> Sort
  -> m Term
declare name sort = do
  symbol <- mkStringSymbol name
  sort' <- compileSort sort
  decl <- mkFuncDecl symbol [] sort'
  Var name <$> mkApp decl []

declareFunction ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Text
  -> [Sort]
  -> Sort
  -> m Function
declareFunction name args sort = do
  symbol <- mkStringSymbol name
  args' <- traverse compileSort args
  sort' <- compileSort sort
  decl <- mkFuncDecl symbol args' sort'
  let func = Function name args sort
  writeFunctionCache func decl
  pure func


--------------------------------------------------------------------------------
-- Terms
-------------------------------------------------------------------------------

compileTerm ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Term
  -> m Z3.AST
compileTerm = \case
  Add es ->
    vararg es mkAdd

  And es ->
    vararg es mkAnd

  Apply f es -> do
    decl <- readFunctionCache f
    as <- traverse compileTerm es
    mkApp decl as

  Distinct es ->
    vararg es mkDistinct

  Eq e1 e2 ->
    binop e1 e2 mkEq

  Ge e1 e2 ->
    binop e1 e2 mkGe

  Gt e1 e2 ->
    binop e1 e2 mkGt

  Iff e1 e2 ->
    binop e1 e2 mkIff

  Implies e1 e2 ->
    binop e1 e2 mkImplies

  Ite e1 e2 e3 ->
    trinop e1 e2 e3 mkIte

  Lit lit ->
    compileLit lit

  Le e1 e2 ->
    binop e1 e2 mkLe

  Lt e1 e2 ->
    binop e1 e2 mkLt

  Negate e ->
    unop e mkUnaryMinus

  Not e ->
    unop e mkNot

  Mul es ->
    vararg es mkMul

  Or es ->
    vararg es mkOr

  Sub es ->
    vararg es mkSub

  Var _name var ->
    pure var

  Xor e1 e2 ->
    binop e1 e2 mkXor

  where
    unop e f =
      compileTerm e >>= f

    binop e1 e2 f = do
      a1 <- compileTerm e1
      a2 <- compileTerm e2
      f a1 a2

    trinop e1 e2 e3 f = do
      a1 <- compileTerm e1
      a2 <- compileTerm e2
      a3 <- compileTerm e3
      f a1 a2 a3

    vararg es f =
      traverse compileTerm es >>= f

compileLit ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Lit
  -> m Z3.AST
compileLit = \case
  LitBool b ->
    if b then mkTrue else mkFalse

  LitInt n ->
    mkInteger n

compileSort ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Sort
  -> m Z3.Sort
compileSort = \case
  SortBool ->
    mkBoolSort

  SortInt ->
    mkIntSort


--------------------------------------------------------------------------------
-- Solver
--------------------------------------------------------------------------------

assert ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Term
  -> m ()
assert =
  compileTerm >=> solverAssertCnstr

frame ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => m a
  -> m a
frame action =
  send (Frame action pure)

check ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => m Z3.Result
check =
  send (SolverCheck pure)

printModel ::
     ( Carrier sig m
     , Member Z3 sig
     , MonadIO m
     )
  => Z3.Model
  -> m ()
printModel model = do
  string <- modelToString model
  traverse_ (Text.putStrLn >>> liftIO) (Text.lines string)


--------------------------------------------------------------------------------
-- Effect smart constructors
--------------------------------------------------------------------------------

getModel ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => m Z3.Model
getModel =
  send (SolverGetModel pure)

mkAdd ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => [Z3.AST]
  -> m Z3.AST
mkAdd as =
  send (MkAdd as pure)

mkAnd ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => [Z3.AST]
  -> m Z3.AST
mkAnd as =
  send (MkAnd as pure)

mkApp ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Z3.FuncDecl
  -> [Z3.AST]
  -> m Z3.AST
mkApp decl args =
  send (MkApp decl args pure)

mkBoolSort ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => m Z3.Sort
mkBoolSort =
  send (MkBoolSort pure)

mkDistinct ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => [Z3.AST]
  -> m Z3.AST
mkDistinct as =
  send (MkDistinct as pure)

mkEq ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Z3.AST
  -> Z3.AST
  -> m Z3.AST
mkEq a1 a2 =
  send (MkEq a1 a2 pure)

mkFalse ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => m Z3.AST
mkFalse =
  send (MkFalse pure)

mkFuncDecl ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Z3.Symbol
  -> [Z3.Sort]
  -> Z3.Sort
  -> m Z3.FuncDecl
mkFuncDecl symbol args sort =
  send (MkFuncDecl symbol args sort pure)

mkGe ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Z3.AST
  -> Z3.AST
  -> m Z3.AST
mkGe a1 a2 =
  send (MkGe a1 a2 pure)

mkGt ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Z3.AST
  -> Z3.AST
  -> m Z3.AST
mkGt a1 a2 =
  send (MkGt a1 a2 pure)

mkIff ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Z3.AST
  -> Z3.AST
  -> m Z3.AST
mkIff a1 a2 =
  send (MkIff a1 a2 pure)

mkImplies ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Z3.AST
  -> Z3.AST
  -> m Z3.AST
mkImplies a1 a2 =
  send (MkImplies a1 a2 pure)

mkInteger ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Integer
  -> m Z3.AST
mkInteger n =
  send (MkInteger n pure)

mkIntSort ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => m Z3.Sort
mkIntSort =
  send (MkIntSort pure)

mkIte ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Z3.AST
  -> Z3.AST
  -> Z3.AST
  -> m Z3.AST
mkIte a1 a2 a3 =
  send (MkIte a1 a2 a3 pure)

mkLe ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Z3.AST
  -> Z3.AST
  -> m Z3.AST
mkLe a1 a2 =
  send (MkLe a1 a2 pure)

mkLt ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Z3.AST
  -> Z3.AST
  -> m Z3.AST
mkLt a1 a2 =
  send (MkLt a1 a2 pure)

mkMul ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => [Z3.AST]
  -> m Z3.AST
mkMul as =
  send (MkMul as pure)

mkNot ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Z3.AST
  -> m Z3.AST
mkNot as =
  send (MkNot as pure)

mkOr ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => [Z3.AST]
  -> m Z3.AST
mkOr as =
  send (MkOr as pure)

mkStringSymbol ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Text
  -> m Z3.Symbol
mkStringSymbol s =
  send (MkStringSymbol s pure)

mkSub ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => [Z3.AST]
  -> m Z3.AST
mkSub as =
  send (MkSub as pure)

mkTrue ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => m Z3.AST
mkTrue =
  send (MkTrue pure)

mkUnaryMinus ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Z3.AST
  -> m Z3.AST
mkUnaryMinus as =
  send (MkUnaryMinus as pure)

mkXor ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Z3.AST
  -> Z3.AST
  -> m Z3.AST
mkXor a1 a2 =
  send (MkXor a1 a2 pure)

modelToString ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Z3.Model
  -> m Text
modelToString model =
  send (ModelToString model pure)

solverAssertCnstr ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Z3.AST
  -> m ()
solverAssertCnstr ast =
  send (SolverAssertCnstr ast (pure ()))

readFunctionCache ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Function
  -> m Z3.FuncDecl
readFunctionCache func =
  send (ReadFunctionCache func pure)

writeFunctionCache ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Function
  -> Z3.FuncDecl
  -> m ()
writeFunctionCache func decl =
  send (WriteFunctionCache func decl (pure ()))
