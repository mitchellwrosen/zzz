{-# LANGUAGE UndecidableInstances #-}

module Zzz
  ( Z3
  , Z3C
  , runZ3
    -- * Variables
  , mkBoolVar
    -- * Expressions
  , Expr
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
  , (+.)
  , (-.)
  , (*.)
  , Zzz.negate
    -- * Solver
  , assert
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
import Data.Foldable (for_, traverse_)
import Data.IORef
import Data.HashMap.Strict (HashMap)
import Data.Kind (Type)
import Data.Text (Text, pack, unpack)
import Data.Word

import qualified Data.HashMap.Strict as HashMap
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import qualified Z3.Base as Z3


data Z3 (m :: Type -> Type) (k :: Type) where
  MkAdd ::
       [Z3.AST]
    -> (Z3.AST -> k)
    -> Z3 m k

  MkAnd ::
       [Z3.AST]
    -> (Z3.AST -> k)
    -> Z3 m k

  MkBoolSort ::
       (Z3.Sort -> k)
    -> Z3 m k

  MkConst ::
       Z3.Symbol
    -> Z3.Sort
    -> (Z3.AST -> k)
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

  deriving stock (Functor)
  deriving anyclass (HFunctor)

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
  , z3cSymbolCache :: IORef (HashMap Text Z3.Symbol)
  }

handleZ3 :: MonadIO m => Z3CEnv -> Z3 (Z3C m) x -> m x
handleZ3 (Z3CEnv ctx solver _symbolCache) = \case
  MkAdd as k ->
    vararg as k Z3.mkAdd

  MkAnd as k ->
    vararg as k Z3.mkAnd

  MkBoolSort k ->
    nullary k Z3.mkBoolSort

  MkConst symbol sort k ->
    k <$> liftIO (Z3.mkConst ctx symbol sort)

  MkDistinct as k ->
    vararg as k Z3.mkDistinct

  MkEq e1 e2 k ->
    binop e1 e2 k Z3.mkEq

  MkFalse k ->
    nullary k Z3.mkFalse

  MkIff a1 a2 k ->
    binop a1 a2 k Z3.mkIff

  MkImplies a1 a2 k ->
    binop a1 a2 k Z3.mkImplies

  MkIntSymbol n k ->
    k <$> liftIO (Z3.mkIntSymbol ctx n)

  MkIte e1 e2 e3 k ->
    k <$> liftIO (Z3.mkIte ctx e1 e2 e3)

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

  where
    unop a k f =
      k <$> liftIO (f ctx a)

    binop a1 a2 k f =
      k <$> liftIO (f ctx a1 a2)

    nullary k f =
      k <$> liftIO (f ctx)

    vararg as k f =
      k <$> liftIO (f ctx as)


runZ3 ::
     MonadIO m
  => [(Text, Text)] -- ^ Config
  -> Z3C m a
  -> m a
runZ3 params action = do
  ctx :: Z3.Context <-
    liftIO $
      Z3.withConfig $ \config -> do
        for_ params $ \(k, v) ->
          Z3.setParamValue config (unpack k) (unpack v)
        Z3.mkContext config

  solver :: Z3.Solver <-
    liftIO (Z3.mkSolver ctx)

  symbolCache :: IORef (HashMap Text Z3.Symbol) <-
    liftIO (newIORef HashMap.empty)

  runReaderC (unZ3C action) Z3CEnv
    { z3cContext = ctx
    , z3cSolver = solver
    , z3cSymbolCache = symbolCache
    }


--------------------------------------------------------------------------------
-- Expression
-------------------------------------------------------------------------------

data Expr
  = Add [Expr]
  | And [Expr]
  | Distinct [Expr]
  | Eq Expr Expr
  | Iff Expr Expr
  | Implies Expr Expr
  | Ite Expr Expr Expr
  | Lit Bool
  | Negate Expr
  | Mul [Expr]
  | Or [Expr]
  | Not Expr
  | Sub [Expr]
  | Var Z3.AST
  | Xor Expr Expr
  -- div
  -- mod
  -- rem
  -- lt
  -- le
  -- gt
  -- ge
  -- int2real
  -- real2int
  -- isInt

compile ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Expr
  -> m Z3.AST
compile = \case
  Add es ->
    vararg es mkAdd

  And es ->
    vararg es mkAnd

  Distinct es ->
    vararg es mkDistinct

  Eq e1 e2 ->
    binop e1 e2 mkEq

  Iff e1 e2 ->
    binop e1 e2 mkIff

  Implies e1 e2 ->
    binop e1 e2 mkImplies

  Ite e1 e2 e3 ->
    trinop e1 e2 e3 mkIte

  Lit lit ->
    if lit then mkTrue else mkFalse

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

  Var var ->
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


infix 4 =.
(=.) :: Expr -> Expr -> Expr
(=.) =
  Eq

infixr 2 ||.
(||.) :: Expr -> Expr -> Expr
e1 ||. e2 =
  Or [e1, e2]

infixr 3 &&.
(&&.) :: Expr -> Expr -> Expr
e1 &&. e2 =
  And [e1, e2]

infixl 6 +.
(+.) :: Expr -> Expr -> Expr
e1 +. e2 =
  Add [e1, e2]

infixl 6 -.
(-.) :: Expr -> Expr -> Expr
e1 -. e2 =
  Sub [e1, e2]

infixl 7 *.
(*.) :: Expr -> Expr -> Expr
e1 *. e2 =
  Mul [e1, e2]

false :: Expr
false =
  Lit False

true :: Expr
true =
  Lit True

not :: Expr -> Expr
not =
  Not

xor :: Expr -> Expr -> Expr
xor =
  Xor

iff :: Expr -> Expr -> Expr
iff =
  Iff

implies :: Expr -> Expr -> Expr
implies =
  Implies

ite :: Expr -> Expr -> Expr -> Expr
ite =
  Ite

distinct :: [Expr] -> Expr
distinct =
  Distinct

negate :: Expr -> Expr
negate =
  Negate


--------------------------------------------------------------------------------
-- Solver
--------------------------------------------------------------------------------

assert ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Expr
  -> m ()
assert =
  compile >=> solverAssertCnstr

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
-- Z3 API
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

mkBoolSort ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => m Z3.Sort
mkBoolSort =
  send (MkBoolSort pure)

mkBoolVar ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Text
  -> m Expr
mkBoolVar name = do
  symbol <- mkStringSymbol name
  sort <- mkBoolSort
  Var <$> mkConst symbol sort

mkConst ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Z3.Symbol
  -> Z3.Sort
  -> m Z3.AST
mkConst symbol sort =
  send (MkConst symbol sort pure)

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

mkIntSymbol ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => Word32
  -> m Z3.Symbol
mkIntSymbol n =
  send (MkIntSymbol n pure)

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

mkSolver ::
     ( Carrier sig m
     , Member Z3 sig
     )
  => m Z3.Solver
mkSolver =
  send (MkSolver pure)

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
