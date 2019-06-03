module Z3 where

import Control.Effect
import Control.Effect.Carrier
import Data.Kind (Type)
import Data.Text (Text)
import Data.Word

import qualified Z3.Base as Z3


data Z3 (m :: Type -> Type) (k :: Type) where
  AstToString ::
       Z3.AST
    -> (String -> k)
    -> Z3 m k

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

  Simplify ::
       Z3.AST
    -> (Z3.AST -> k)
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
       Text
    -> (Z3.FuncDecl -> k)
    -> Z3 m k

  ReadVarCache ::
       Text
    -> (Z3.AST -> k)
    -> Z3 m k

  WriteFunctionCache ::
       Text
    -> Z3.FuncDecl
    -> k
    -> Z3 m k

  WriteVarCache ::
       Text
    -> Z3.AST
    -> k
    -> Z3 m k

deriving instance Functor (Z3 m)

instance HFunctor Z3 where
  hmap :: (forall x. m x -> n x) -> Z3 m a -> Z3 n a
  hmap f = \case
    AstToString a b -> AstToString a b
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
    MkIntSort a -> MkIntSort a
    MkIntSymbol a b -> MkIntSymbol a b
    MkInteger a b -> MkInteger a b
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
    ReadFunctionCache a b -> ReadFunctionCache a b
    ReadVarCache a b -> ReadVarCache a b
    Simplify a b -> Simplify a b
    SolverAssertCnstr a b -> SolverAssertCnstr a b
    SolverCheck a -> SolverCheck a
    SolverGetModel a -> SolverGetModel a
    WriteFunctionCache a b c -> WriteFunctionCache a b c
    WriteVarCache a b c -> WriteVarCache a b c

astToString ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Z3.AST
  -> m String
astToString ast =
  send (AstToString ast pure)

check ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => m Z3.Result
check =
  send (SolverCheck pure)

frame ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => m a
  -> m a
frame action =
  send (Frame action pure)

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

simplify ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Z3.AST
  -> m Z3.AST
simplify ast =
  send (Simplify ast pure)

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
  => Text
  -> m Z3.FuncDecl
readFunctionCache name =
  send (ReadFunctionCache name pure)

readVarCache ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Text
  -> m Z3.AST
readVarCache var =
  send (ReadVarCache var pure)

writeFunctionCache ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Text
  -> Z3.FuncDecl
  -> m ()
writeFunctionCache name decl =
  send (WriteFunctionCache name decl (pure ()))

writeVarCache ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Text
  -> Z3.AST
  -> m ()
writeVarCache var ast =
  send (WriteVarCache var ast (pure ()))
