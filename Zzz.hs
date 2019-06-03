{-# LANGUAGE UndecidableInstances #-}

module Zzz
  ( Z3
  , Z3C
  , runZ3
    -- * Declarations
  , declare
  , declareFunction
  , Function
    -- * Terms
  , Term
  , (=.)
  , false
  , true
  , Zzz.not
  , (||.)
  , (&&.)
  , xor
  , iff
  , implies
  , ite
  , distinct
  , Zzz.negate
  , (<.)
  , (<=.)
  , (>.)
  , (>=.)
  , apply
    -- * Sorts
  , Sort
  , boolSort
  , intSort
    -- * Solver
  , assert
  , frame
  , check
  , getModel
  , printModel
  , modelToString
  ) where

import Control.Category ((>>>))
import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Reader (ReaderC(..), runReader)
import Control.Effect.Sum
import Control.Monad ((>=>))
import Control.Monad.IO.Class (MonadIO(..))
import Data.Foldable (traverse_)
import Data.Hashable (Hashable)
import Data.HashMap.Strict (HashMap)
import Data.IORef
import Data.Kind (Type)
import Data.List (foldl')
import Data.Text (Text, pack, unpack)
import Data.Word
import GHC.Generics (Generic)

import qualified Data.HashMap.Strict as HashMap
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

newtype Z3C (m :: Type -> Type) (a :: Type)
  = Z3C { unZ3C :: ReaderC Z3CEnv m a }
  deriving newtype (Applicative, Functor, Monad, MonadIO)

instance (Carrier sig m, MonadIO m) => Carrier (Z3 :+: sig) (Z3C m) where
  eff :: (Z3 :+: sig) (Z3C m) (Z3C m a) -> Z3C m a
  eff = \case
    L z3 ->
      Z3C (ReaderC (\env -> handleZ3 env z3 >>= runReader env . unZ3C))

    R other ->
      Z3C (eff (R (handleCoercible other)))

data Z3CEnv
  = Z3CEnv
  { z3cContext :: Z3.Context
  , z3cSolver :: Z3.Solver
  -- , z3cSymbolCache :: IORef (HashMap Text Z3.Symbol)
  , z3cFunctionCache :: IORef (Framed (HashMap Function Z3.FuncDecl))
  }

handleZ3 :: MonadIO m => Z3CEnv -> Z3 (Z3C m) x -> m x
handleZ3 env@(Z3CEnv ctx solver functionCacheRef) = \case
  Frame action k ->
    let
      inframe =
        liftIO do
          modifyIORef' functionCacheRef (pushFrame HashMap.empty)
          Z3.solverPush ctx solver

      outframe =
        liftIO do
          Z3.solverPop ctx solver 1
          modifyIORef' functionCacheRef popFrame
    in
      inframe
        *>
      (k <$> runReader env (unZ3C action))
        <*
      outframe

  MkAdd as k ->
    vararg as k Z3.mkAdd

  MkAnd as k ->
    vararg as k Z3.mkAnd

  MkApp decl args k ->
    k <$> liftIO (Z3.mkApp ctx decl args)

  MkBoolSort k ->
    nullary k Z3.mkBoolSort

  MkDistinct as k ->
    vararg as k Z3.mkDistinct

  MkEq a1 a2 k ->
    binop a1 a2 k Z3.mkEq

  MkFalse k ->
    nullary k Z3.mkFalse

  MkFuncDecl name args sort k ->
    k <$> liftIO (Z3.mkFuncDecl ctx name args sort)

  MkGe a1 a2 k ->
    binop a1 a2 k Z3.mkGe

  MkGt a1 a2 k ->
    binop a1 a2 k Z3.mkGt

  MkIff a1 a2 k ->
    binop a1 a2 k Z3.mkIff

  MkImplies a1 a2 k ->
    binop a1 a2 k Z3.mkImplies

  MkIntSort k ->
    nullary k Z3.mkIntSort

  MkInteger n k ->
    k <$> liftIO (Z3.mkInteger ctx n)

  MkIntSymbol n k ->
    k <$> liftIO (Z3.mkIntSymbol ctx n)

  MkIte a1 a2 a3 k ->
    k <$> liftIO (Z3.mkIte ctx a1 a2 a3)

  MkLe a1 a2 k ->
    binop a1 a2 k Z3.mkLe

  MkLt a1 a2 k ->
    binop a1 a2 k Z3.mkLt

  MkMul as k ->
    vararg as k Z3.mkMul

  MkNot a k ->
    unop a k Z3.mkNot

  MkOr as k ->
    vararg as k Z3.mkOr

  MkSolver k ->
    nullary k Z3.mkSolver

  MkStringSymbol s k ->
    k <$> liftIO (Z3.mkStringSymbol ctx (unpack s))

  MkSub as k ->
    vararg as k Z3.mkSub

  MkTrue k ->
    nullary k Z3.mkTrue

  MkUnaryMinus a k ->
    unop a k Z3.mkUnaryMinus

  MkXor a1 a2 k ->
    binop a1 a2 k Z3.mkXor

  ModelToString model k ->
    k . pack <$> liftIO (Z3.modelToString ctx model)

  SolverAssertCnstr ast k -> do
    liftIO (Z3.solverAssertCnstr ctx solver ast)
    pure k

  SolverCheck k ->
    k <$> liftIO (Z3.solverCheck ctx solver)

  SolverGetModel k ->
    k <$> liftIO (Z3.solverGetModel ctx solver)

  ReadFunctionCache func k -> do
    cache <- liftIO (readIORef functionCacheRef)

    let
      foldedCache =
        foldlFramed HashMap.union HashMap.empty cache

    case HashMap.lookup func foldedCache of
      Nothing ->
        error $ "Undefined function: " ++ show func

      Just decl ->
        pure (k decl)

  WriteFunctionCache func decl k -> do
    liftIO
      (modifyIORef'
        functionCacheRef
        (modifyFramed (HashMap.insert func decl)))
    pure k

  where
    unop a k f =
      k <$> liftIO (f ctx a)

    binop a1 a2 k f =
      k <$> liftIO (f ctx a1 a2)

    nullary :: MonadIO m => (a -> b) -> (Z3.Context -> IO a) -> m b
    nullary k f =
      k <$> liftIO (f ctx)

    vararg as k f =
      k <$> liftIO (f ctx as)


runZ3 ::
     MonadIO m
  => Z3C m a
  -> m a
runZ3 action = do
  ctx :: Z3.Context <-
    liftIO (Z3.withConfig Z3.mkContext)

  solver :: Z3.Solver <-
    liftIO (Z3.mkSolver ctx)

  functionCache :: IORef (Framed (HashMap Function Z3.FuncDecl)) <-
    liftIO (newIORef (newFramed HashMap.empty))

  -- symbolCache :: IORef (HashMap Text Z3.Symbol) <-
  --   liftIO (newIORef HashMap.empty)

  runReaderC (unZ3C action) Z3CEnv
    { z3cContext = ctx
    , z3cSolver = solver
    , z3cFunctionCache = functionCache
    -- , z3cSymbolCache = symbolCache
    }


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

--------------------------------------------------------------------------------
-- Declarations
-------------------------------------------------------------------------------

data Function
  = Function Text [Sort] Sort
  deriving stock (Eq, Generic, Show)
  deriving anyclass (Hashable)

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

data Term
  = Add [Term]
  | And [Term]
  | Apply Function [Term]
  | Distinct [Term]
  | Eq Term Term
  | Ge Term Term
  | Gt Term Term
  | Iff Term Term
  | Implies Term Term
  | Ite Term Term Term
  | Lit Lit
  | Le Term Term
  | Lt Term Term
  | Negate Term
  | Mul [Term]
  | Or [Term]
  | Not Term
  | Sub [Term]
  | Var Text Z3.AST
  | Xor Term Term

  -- div
  -- mod
  -- rem
  -- int2real
  -- real2int
  -- isInt

data Lit
  = LitBool Bool
  | LitInt Integer

instance Num Term where
  fromInteger =
    Lit . LitInt

  e1 + e2 =
    Add [e1, e2]

  e1 * e2 =
    Mul [e1, e2]

  e1 - e2 =
    Sub [e1, e2]


compile ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Term
  -> m Z3.AST
compile = \case
  Add es ->
    vararg es mkAdd

  And es ->
    vararg es mkAnd

  Apply f es -> do
    decl <- readFunctionCache f
    as <- traverse compile es
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
      compile e >>= f

    binop e1 e2 f = do
      a1 <- compile e1
      a2 <- compile e2
      f a1 a2

    trinop e1 e2 e3 f = do
      a1 <- compile e1
      a2 <- compile e2
      a3 <- compile e3
      f a1 a2 a3

    vararg es f =
      traverse compile es >>= f

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


infix 4 =.
(=.) :: Term -> Term -> Term
(=.) =
  Eq

infixr 2 ||.
(||.) :: Term -> Term -> Term
e1 ||. e2 =
  Or [e1, e2]

infixr 3 &&.
(&&.) :: Term -> Term -> Term
e1 &&. e2 =
  And [e1, e2]

infix 4 <.
(<.) :: Term -> Term -> Term
(<.) =
  Lt

infix 4 <=.
(<=.) :: Term -> Term -> Term
(<=.) =
  Le

infix 4 >.
(>.) :: Term -> Term -> Term
(>.) =
  Gt

infix 4 >=.
(>=.) :: Term -> Term -> Term
(>=.) =
  Ge

false :: Term
false =
  Lit (LitBool False)

true :: Term
true =
  Lit (LitBool True)

not :: Term -> Term
not =
  Not

xor :: Term -> Term -> Term
xor =
  Xor

iff :: Term -> Term -> Term
iff =
  Iff

implies :: Term -> Term -> Term
implies =
  Implies

ite :: Term -> Term -> Term -> Term
ite =
  Ite

distinct :: [Term] -> Term
distinct =
  Distinct

negate :: Term -> Term
negate =
  Negate

apply :: Function -> [Term] -> Term
apply =
  Apply


--------------------------------------------------------------------------------
-- Sorts
--------------------------------------------------------------------------------

data Sort
  = SortBool
  | SortInt
  deriving stock (Eq, Generic, Show)
  deriving anyclass (Hashable)

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

boolSort :: Sort
boolSort =
  SortBool

intSort :: Sort
intSort =
  SortInt

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
  compile >=> solverAssertCnstr

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
