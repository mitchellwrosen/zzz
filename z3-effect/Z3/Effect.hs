{-# LANGUAGE UndecidableInstances #-}

module Z3.Effect
  ( -- * Effect
    Z3(..)
  , Z3.Effect.addConstInterp
  , Z3.Effect.addFuncInterp
  , Z3.Effect.andThenTactic
  , Z3.Effect.appToAst
  , Z3.Effect.applyTactic
  , Z3.Effect.astToString
  , Z3.Effect.benchmarkToSMTLibString
  , Z3.Effect.fixedpointAddRule
  , Z3.Effect.fixedpointGetAnswer
  , Z3.Effect.fixedpointGetAssertions
  , Z3.Effect.fixedpointPop
  , Z3.Effect.fixedpointPush
  , Z3.Effect.fixedpointQueryRelations
  , Z3.Effect.fixedpointRegisterRelation
  , Z3.Effect.fixedpointSetParams
  , Z3.Effect.funcDeclToString
  , Z3.Effect.funcEntryGetArg
  , Z3.Effect.funcEntryGetNumArgs
  , Z3.Effect.funcEntryGetValue
  , Z3.Effect.funcInterpGetArity
  , Z3.Effect.funcInterpGetElse
  , Z3.Effect.funcInterpGetEntry
  , Z3.Effect.funcInterpGetNumEntries
  , Z3.Effect.getAppArg
  , Z3.Effect.getAppDecl
  , Z3.Effect.getAppNumArgs
  , Z3.Effect.getApplyResultNumSubgoals
  , Z3.Effect.getApplyResultSubgoal
  , Z3.Effect.getArity
  , Z3.Effect.getArraySortDomain
  , Z3.Effect.getArraySortRange
  , Z3.Effect.getAsArrayFuncDecl
  , Z3.Effect.getAstKind
  , Z3.Effect.getBoolValue
  , Z3.Effect.getBvSortSize
  , Z3.Effect.getConstDecl
  , Z3.Effect.getConstInterp
  -- , Z3.Effect.getDatatypeSortConstructorAccessors
  -- , Z3.Effect.getDatatypeSortConstructors
  -- , Z3.Effect.getDatatypeSortRecognizers
  -- , Z3.Effect.getDeclName
  -- , Z3.Effect.getDomain
  -- , Z3.Effect.getFuncDecl
  -- , Z3.Effect.getFuncInterp
  -- , Z3.Effect.getFuncs
  -- , Z3.Effect.getGoalFormula
  -- , Z3.Effect.getGoalFormulas
  -- , Z3.Effect.getGoalSize
  -- , Z3.Effect.getIndexValue
  -- , Z3.Effect.getNumeralString
  -- , Z3.Effect.getQuantifierBody
  -- , Z3.Effect.getQuantifierBoundName
  -- , Z3.Effect.getQuantifierBoundSort
  -- , Z3.Effect.getQuantifierBoundVars
  -- , Z3.Effect.getQuantifierNoPatternAST
  -- , Z3.Effect.getQuantifierNoPatterns
  -- , Z3.Effect.getQuantifierNumBound
  -- , Z3.Effect.getQuantifierNumNoPatterns
  -- , Z3.Effect.getQuantifierNumPatterns
  -- , Z3.Effect.getQuantifierPatternAST
  -- , Z3.Effect.getQuantifierPatterns
  -- , Z3.Effect.getQuantifierWeight
  -- , Z3.Effect.getRange
  -- , Z3.Effect.getSort
  -- , Z3.Effect.getSortKind
  -- , Z3.Effect.getSymbolString
  -- , Z3.Effect.goalAssert
  -- , Z3.Effect.hasInterp
  -- , Z3.Effect.isApp
  -- , Z3.Effect.isAsArray
  -- , Z3.Effect.isQuantifierExists
  -- , Z3.Effect.isQuantifierForall
  , Z3.Effect.mkAdd
  , Z3.Effect.mkAnd
  -- , Z3.Effect.mkAndInverterGraphTactic
  , Z3.Effect.mkApp
  -- , Z3.Effect.mkArrayDefault
  , Z3.Effect.mkArraySort
  , Z3.Effect.mkBoolSort
  -- , Z3.Effect.mkBound
  -- , Z3.Effect.mkBsge
  -- , Z3.Effect.mkBsgt
  -- , Z3.Effect.mkBuge
  -- , Z3.Effect.mkBugt
  -- , Z3.Effect.mkBv2int
  -- , Z3.Effect.mkBvSort
  -- , Z3.Effect.mkBvadd
  -- , Z3.Effect.mkBvaddNoOverflow
  -- , Z3.Effect.mkBvaddNoUnderflow
  -- , Z3.Effect.mkBvand
  -- , Z3.Effect.mkBvashr
  -- , Z3.Effect.mkBvlshr
  -- , Z3.Effect.mkBvmul
  -- , Z3.Effect.mkBvmulNoOverflow
  -- , Z3.Effect.mkBvmulNoUnderflow
  -- , Z3.Effect.mkBvnand
  -- , Z3.Effect.mkBvneg
  -- , Z3.Effect.mkBvnegNoOverflow
  -- , Z3.Effect.mkBvnot
  -- , Z3.Effect.mkBvor
  -- , Z3.Effect.mkBvredand
  -- , Z3.Effect.mkBvredor
  -- , Z3.Effect.mkBvsdiv
  -- , Z3.Effect.mkBvsdivNoOverflow
  -- , Z3.Effect.mkBvshl
  -- , Z3.Effect.mkBvsle
  -- , Z3.Effect.mkBvslt
  -- , Z3.Effect.mkBvsmod
  -- , Z3.Effect.mkBvsrem
  -- , Z3.Effect.mkBvsub
  -- , Z3.Effect.mkBvsubNoOverflow
  -- , Z3.Effect.mkBvsubNoUnderflow
  -- , Z3.Effect.mkBvudiv
  -- , Z3.Effect.mkBvule
  -- , Z3.Effect.mkBvult
  -- , Z3.Effect.mkBvurem
  -- , Z3.Effect.mkBvxnor
  -- , Z3.Effect.mkBvxor
  -- , Z3.Effect.mkConcat
  -- , Z3.Effect.mkConst
  -- , Z3.Effect.mkConstArray
  -- , Z3.Effect.mkConstructor
  -- , Z3.Effect.mkDatatype
  -- , Z3.Effect.mkDatatypes
  , Z3.Effect.mkDistinct
  -- , Z3.Effect.mkDiv
  -- , Z3.Effect.mkEmptySet
  , Z3.Effect.mkEq
  -- , Z3.Effect.mkExists
  -- , Z3.Effect.mkExistsConst
  -- , Z3.Effect.mkExtRotateLeft
  -- , Z3.Effect.mkExtRotateRight
  -- , Z3.Effect.mkExtract
  , Z3.Effect.mkFalse
  -- , Z3.Effect.mkFiniteDomainSort
  -- , Z3.Effect.mkFixedpoint
  -- , Z3.Effect.mkForall
  -- , Z3.Effect.mkForallConst
  -- , Z3.Effect.mkFreshConst
  -- , Z3.Effect.mkFreshFuncDecl
  -- , Z3.Effect.mkFullSet
  , Z3.Effect.mkFuncDecl
  , Z3.Effect.mkGe
  -- , Z3.Effect.mkGoal
  , Z3.Effect.mkGt
  , Z3.Effect.mkIff
  , Z3.Effect.mkImplies
  -- , Z3.Effect.mkInt
  -- , Z3.Effect.mkInt2Real
  -- , Z3.Effect.mkInt2bv
  -- , Z3.Effect.mkInt64
  , Z3.Effect.mkIntSort
  , Z3.Effect.mkIntSymbol
  , Z3.Effect.mkInteger
  -- , Z3.Effect.mkIsInt
  , Z3.Effect.mkIte
  , Z3.Effect.mkLe
  , Z3.Effect.mkLt
  -- , Z3.Effect.mkMap
  -- , Z3.Effect.mkMod
  , Z3.Effect.mkMul
  , Z3.Effect.mkNot
  -- , Z3.Effect.mkNumeral
  , Z3.Effect.mkOr
  , Z3.Effect.mkParams
  -- , Z3.Effect.mkPattern
  -- , Z3.Effect.mkQuantifierEliminationTactic
  -- , Z3.Effect.mkReal
  -- , Z3.Effect.mkReal2Int
  -- , Z3.Effect.mkRealSort
  -- , Z3.Effect.mkRem
  -- , Z3.Effect.mkRepeat
  -- , Z3.Effect.mkRotateLeft
  -- , Z3.Effect.mkRotateRight
  -- , Z3.Effect.mkSelect
  -- , Z3.Effect.mkSetAdd
  -- , Z3.Effect.mkSetComplement
  -- , Z3.Effect.mkSetDel
  -- , Z3.Effect.mkSetDifference
  -- , Z3.Effect.mkSetIntersect
  -- , Z3.Effect.mkSetMember
  -- , Z3.Effect.mkSetSort
  -- , Z3.Effect.mkSetSubset
  -- , Z3.Effect.mkSetUnion
  -- , Z3.Effect.mkSignExt
  -- , Z3.Effect.mkSimpleSolver
  -- , Z3.Effect.mkSolver
  -- , Z3.Effect.mkSolverForLogic
  , Z3.Effect.mkStore
  , Z3.Effect.mkStringSymbol
  , Z3.Effect.mkSub
  -- , Z3.Effect.mkTactic
  , Z3.Effect.mkTrue
  -- , Z3.Effect.mkTupleSort
  , Z3.Effect.mkUnaryMinus
  -- , Z3.Effect.mkUninterpretedSort
  -- , Z3.Effect.mkUnsignedInt
  -- , Z3.Effect.mkUnsignedInt64
  , Z3.Effect.mkXor
  -- , Z3.Effect.mkZeroExt
  -- , Z3.Effect.modelEval
  , Z3.Effect.modelToString
  -- , Z3.Effect.numConsts
  -- , Z3.Effect.numFuncs
  -- , Z3.Effect.orElseTactic
  , Z3.Effect.paramsSetBool
  , Z3.Effect.paramsSetDouble
  , Z3.Effect.paramsSetSymbol
  , Z3.Effect.paramsSetUInt
  , Z3.Effect.paramsToString
  -- , Z3.Effect.parseSMTLib2File
  -- , Z3.Effect.parseSMTLib2String
  -- , Z3.Effect.patternToString
  -- , Z3.Effect.setASTPrintMode
  , Z3.Effect.simplify
  -- , Z3.Effect.simplifyEx
  -- , Z3.Effect.skipTactic
  -- , Z3.Effect.solverAssertAndTrack
  , Z3.Effect.solverAssertCnstr
  , Z3.Effect.solverCheck
  -- , Z3.Effect.solverCheck
  -- , Z3.Effect.solverCheckAssumptions
  -- , Z3.Effect.solverGetHelp
  , Z3.Effect.solverGetModel
  -- , Z3.Effect.solverGetNumScopes
  -- , Z3.Effect.solverGetReasonUnknown
  -- , Z3.Effect.solverGetUnsatCore
  -- , Z3.Effect.solverPop
  -- , Z3.Effect.solverPush
  -- , Z3.Effect.solverReset
  -- , Z3.Effect.solverSetParams
  -- , Z3.Effect.solverToString
  -- , Z3.Effect.sortToString
  -- , Z3.Effect.substituteVars
  -- , Z3.Effect.toApp
  -- , Z3.Effect.tryForTactic
    -- * Carrier
  , Z3C
  , runZ3

    -- * Re-exports
  , App
  , ApplyResult
  , AST
  , ASTKind(..)
  , ASTPrintMode(..)
  -- , Config
  , Constructor
  , Context
  , Fixedpoint(..)
  , FuncDecl
  , FuncEntry
  , FuncInterp
  , Goal
  , Logic(..)
  , Model
  , Params
  , Pattern
  , Result(..)
  -- , Solver
  , Sort
  , SortKind(..)
  , Symbol
  , Tactic
  , Version(..)
  , Z3Error(..)
  , Z3ErrorCode(..)
  ) where

import Control.Effect
import Control.Effect.Carrier
import Control.Effect.Error
import Control.Effect.Reader (ReaderC(..), runReader)
import Control.Effect.Sum
import Control.Exception (try)
import Control.Monad.IO.Class (MonadIO(..))
import Data.Kind (Type)
import Z3.Base as Z3


data Z3 (m :: Type -> Type) (k :: Type)
  = AddConstInterp Model FuncDecl AST k
  | AddFuncInterp Model FuncDecl AST (FuncInterp -> k)
  | AndThenTactic Tactic Tactic (Tactic -> k)
  | AppToAst App (AST -> k)
  | ApplyTactic Tactic Goal (ApplyResult -> k)
  | AstToString AST (String -> k)
  | BenchmarkToSMTLibString String String String String [AST] AST (String -> k)
  | FixedpointAddRule Fixedpoint AST Symbol k
  | FixedpointGetAnswer Fixedpoint (AST -> k)
  | FixedpointGetAssertions Fixedpoint ([AST] -> k)
  | FixedpointPop Fixedpoint k
  | FixedpointPush Fixedpoint k
  | FixedpointQueryRelations Fixedpoint [FuncDecl] (Result -> k)
  | FixedpointRegisterRelation Fixedpoint FuncDecl k
  | FixedpointSetParams Fixedpoint Params k
  | FuncDeclToString FuncDecl (String -> k)
  | FuncEntryGetArg FuncEntry Int (AST -> k)
  | FuncEntryGetNumArgs FuncEntry (Int -> k)
  | FuncEntryGetValue FuncEntry (AST -> k)
  | FuncInterpGetArity FuncInterp (Int -> k)
  | FuncInterpGetElse FuncInterp (AST -> k)
  | FuncInterpGetEntry FuncInterp Int (FuncEntry -> k)
  | FuncInterpGetNumEntries FuncInterp (Int -> k)
  | GetAppArg App Int (AST -> k)
  | GetAppDecl App (FuncDecl -> k)
  | GetAppNumArgs App (Int -> k)
  | GetApplyResultNumSubgoals ApplyResult (Int -> k)
  | GetApplyResultSubgoal ApplyResult Int (Goal -> k)
  | GetArity FuncDecl (Int -> k)
  | GetArraySortDomain Sort (Sort -> k)
  | GetArraySortRange Sort (Sort -> k)
  | GetAsArrayFuncDecl AST (FuncDecl -> k)
  | GetAstKind AST (ASTKind -> k)
  | GetBoolValue AST (Maybe Bool -> k)
  | GetBvSortSize Sort (Int -> k)
  | GetConstDecl Model Word (FuncDecl -> k)
  | GetConstInterp Model FuncDecl (Maybe AST -> k)
  | MkAdd [AST] (AST -> k)
  | MkAnd [AST] (AST -> k)
  | MkApp FuncDecl [AST] (AST -> k)
  | MkArraySort Sort Sort (Sort -> k)
  | MkBoolSort (Sort -> k)
  | MkDistinct [AST] (AST -> k)
  | MkEq AST AST (AST -> k)
  | MkFalse (AST -> k)
  | MkFuncDecl Symbol [Sort] Sort (FuncDecl -> k)
  | MkGe AST AST (AST -> k)
  | MkGt AST AST (AST -> k)
  | MkIff AST AST (AST -> k)
  | MkImplies AST AST (AST -> k)
  | MkInteger Integer (AST -> k)
  | MkIntSort (Sort -> k)
  | forall a. Integral a => MkIntSymbol a (Symbol -> k)
  | MkIte AST AST AST (AST -> k)
  | MkLe AST AST (AST -> k)
  | MkLt AST AST (AST -> k)
  | MkMul [AST] (AST -> k)
  | MkNot AST (AST -> k)
  | MkOr [AST] (AST -> k)
  | MkParams (Params -> k)
  | MkSolver (Solver -> k)
  | MkStore AST AST AST (AST -> k)
  | MkStringSymbol String (Symbol -> k)
  | MkSub [AST] (AST -> k)
  | MkTrue (AST -> k)
  | MkUnaryMinus AST (AST -> k)
  | MkXor AST AST (AST -> k)
  | ModelToString Model (String -> k)
  | ParamsSetBool Params Symbol Bool k
  | ParamsSetDouble Params Symbol Double k
  | ParamsSetSymbol Params Symbol Symbol k
  | ParamsSetUInt Params Symbol Word k
  | ParamsToString Params (String -> k)
  | Simplify AST (AST -> k)
  | SolverAssertCnstr AST k
  | SolverCheck (Result -> k)
  | SolverGetModel (Model -> k)
  deriving anyclass (HFunctor)

deriving stock instance Functor (Z3 m)


addConstInterp :: (Carrier sig m, Member Z3 sig) => Model -> FuncDecl -> AST -> m ()
addConstInterp = func3_ AddConstInterp

addFuncInterp :: (Carrier sig m, Member Z3 sig) => Model -> FuncDecl -> AST -> m FuncInterp
addFuncInterp = func3 AddFuncInterp

andThenTactic :: (Carrier sig m, Member Z3 sig) => Tactic -> Tactic -> m Tactic
andThenTactic = func2 AndThenTactic

appToAst :: (Carrier sig m, Member Z3 sig) => App -> m AST
appToAst = func1 AppToAst

applyTactic :: (Carrier sig m, Member Z3 sig) => Tactic -> Goal -> m ApplyResult
applyTactic = func2 ApplyTactic

astToString :: (Carrier sig m, Member Z3 sig) => AST -> m String
astToString = func1 AstToString

benchmarkToSMTLibString :: (Carrier sig m, Member Z3 sig) => String -> String -> String -> String -> [AST] -> AST -> m String
benchmarkToSMTLibString = func6 BenchmarkToSMTLibString

fixedpointAddRule :: (Carrier sig m, Member Z3 sig) => Fixedpoint -> AST -> Symbol -> m ()
fixedpointAddRule = func3_ FixedpointAddRule

fixedpointGetAnswer :: (Carrier sig m, Member Z3 sig) => Fixedpoint -> m AST
fixedpointGetAnswer = func1 FixedpointGetAnswer

fixedpointGetAssertions :: (Carrier sig m, Member Z3 sig) => Fixedpoint -> m [AST]
fixedpointGetAssertions = func1 FixedpointGetAssertions

fixedpointPop :: (Carrier sig m, Member Z3 sig) => Fixedpoint -> m ()
fixedpointPop = func1_ FixedpointPop

fixedpointPush :: (Carrier sig m, Member Z3 sig) => Fixedpoint -> m ()
fixedpointPush = func1_ FixedpointPush

fixedpointQueryRelations :: (Carrier sig m, Member Z3 sig) => Fixedpoint -> [FuncDecl] -> m Result
fixedpointQueryRelations = func2 FixedpointQueryRelations

fixedpointRegisterRelation :: (Carrier sig m, Member Z3 sig) => Fixedpoint -> FuncDecl -> m ()
fixedpointRegisterRelation = func2_ FixedpointRegisterRelation

fixedpointSetParams :: (Carrier sig m, Member Z3 sig) => Fixedpoint -> Params -> m ()
fixedpointSetParams = func2_ FixedpointSetParams

funcDeclToString :: (Carrier sig m, Member Z3 sig) => FuncDecl -> m String
funcDeclToString = func1 FuncDeclToString

funcEntryGetArg :: (Carrier sig m, Member Z3 sig) => FuncEntry -> Int -> m AST
funcEntryGetArg = func2 FuncEntryGetArg

funcEntryGetNumArgs :: (Carrier sig m, Member Z3 sig) => FuncEntry -> m Int
funcEntryGetNumArgs = func1 FuncEntryGetNumArgs

funcEntryGetValue :: (Carrier sig m, Member Z3 sig) => FuncEntry -> m AST
funcEntryGetValue = func1 FuncEntryGetValue

funcInterpGetArity :: (Carrier sig m, Member Z3 sig) => FuncInterp -> m Int
funcInterpGetArity = func1 FuncInterpGetArity

funcInterpGetElse :: (Carrier sig m, Member Z3 sig) => FuncInterp -> m AST
funcInterpGetElse = func1 FuncInterpGetElse

funcInterpGetEntry :: (Carrier sig m, Member Z3 sig) => FuncInterp -> Int -> m FuncEntry
funcInterpGetEntry = func2 FuncInterpGetEntry

funcInterpGetNumEntries :: (Carrier sig m, Member Z3 sig) => FuncInterp -> m Int
funcInterpGetNumEntries = func1 FuncInterpGetNumEntries

getAppArg :: (Carrier sig m, Member Z3 sig) => App -> Int -> m AST
getAppArg = func2 GetAppArg

getAppDecl :: (Carrier sig m, Member Z3 sig) => App -> m FuncDecl
getAppDecl = func1 GetAppDecl

getAppNumArgs :: (Carrier sig m, Member Z3 sig) => App -> m Int
getAppNumArgs = func1 GetAppNumArgs

getApplyResultNumSubgoals :: (Carrier sig m, Member Z3 sig) => ApplyResult -> m Int
getApplyResultNumSubgoals = func1 GetApplyResultNumSubgoals

getApplyResultSubgoal :: (Carrier sig m, Member Z3 sig) => ApplyResult -> Int -> m Goal
getApplyResultSubgoal = func2 GetApplyResultSubgoal

getArity :: (Carrier sig m, Member Z3 sig) => FuncDecl -> m Int
getArity = func1 GetArity

getArraySortDomain :: (Carrier sig m, Member Z3 sig) => Sort -> m Sort
getArraySortDomain = func1 GetArraySortDomain

getArraySortRange :: (Carrier sig m, Member Z3 sig) => Sort -> m Sort
getArraySortRange = func1 GetArraySortRange

getAsArrayFuncDecl :: (Carrier sig m, Member Z3 sig) => AST -> m FuncDecl
getAsArrayFuncDecl = func1 GetAsArrayFuncDecl

getAstKind :: (Carrier sig m, Member Z3 sig) => AST -> m ASTKind
getAstKind = func1 GetAstKind

getBoolValue :: (Carrier sig m, Member Z3 sig) => AST -> m (Maybe Bool)
getBoolValue = func1 GetBoolValue

getBvSortSize :: (Carrier sig m, Member Z3 sig) => Sort -> m Int
getBvSortSize = func1 GetBvSortSize

getConstDecl :: (Carrier sig m, Member Z3 sig) => Model -> Word -> m FuncDecl
getConstDecl = func2 GetConstDecl

getConstInterp :: (Carrier sig m, Member Z3 sig) => Model -> FuncDecl -> m (Maybe AST)
getConstInterp = func2 GetConstInterp

mkAdd :: (Carrier sig m, Member Z3 sig) => [AST] -> m AST
mkAdd = func1 MkAdd

mkAnd :: (Carrier sig m, Member Z3 sig) => [AST] -> m AST
mkAnd = func1 MkAnd

mkApp :: (Carrier sig m, Member Z3 sig) => FuncDecl -> [AST] -> m AST
mkApp = func2 MkApp

mkArraySort :: (Carrier sig m, Member Z3 sig) => Sort -> Sort -> m Sort
mkArraySort = func2 MkArraySort

mkBoolSort :: (Carrier sig m, Member Z3 sig) => m Sort
mkBoolSort = func0 MkBoolSort

mkDistinct :: (Carrier sig m, Member Z3 sig) => [AST] -> m AST
mkDistinct = func1 MkDistinct

mkEq :: (Carrier sig m, Member Z3 sig) => AST -> AST -> m AST
mkEq = func2 MkEq

mkFalse :: (Carrier sig m, Member Z3 sig) => m AST
mkFalse = func0 MkFalse

mkFuncDecl :: (Carrier sig m, Member Z3 sig) => Symbol -> [Sort] -> Sort -> m FuncDecl
mkFuncDecl = func3 MkFuncDecl

mkGe :: (Carrier sig m, Member Z3 sig) => AST -> AST -> m AST
mkGe = func2 MkGe

mkGt :: (Carrier sig m, Member Z3 sig) => AST -> AST -> m AST
mkGt = func2 MkGt

mkIff :: (Carrier sig m, Member Z3 sig) => AST -> AST -> m AST
mkIff = func2 MkIff

mkImplies :: (Carrier sig m, Member Z3 sig) => AST -> AST -> m AST
mkImplies = func2 MkImplies

mkInteger :: (Carrier sig m, Member Z3 sig) => Integer -> m AST
mkInteger = func1 MkInteger

mkIntSort :: (Carrier sig m, Member Z3 sig) => m Sort
mkIntSort = func0 MkIntSort

mkIntSymbol :: (Integral a, Carrier sig m, Member Z3 sig) => a -> m Symbol
mkIntSymbol = func1 MkIntSymbol

mkIte :: (Carrier sig m, Member Z3 sig) => AST -> AST -> AST -> m AST
mkIte = func3 MkIte

mkLe :: (Carrier sig m, Member Z3 sig) => AST -> AST -> m AST
mkLe = func2 MkLe

mkLt :: (Carrier sig m, Member Z3 sig) => AST -> AST -> m AST
mkLt = func2 MkLt

mkMul :: (Carrier sig m, Member Z3 sig) => [AST] -> m AST
mkMul = func1 MkMul

mkNot :: (Carrier sig m, Member Z3 sig) => AST -> m AST
mkNot = func1 MkNot

mkOr :: (Carrier sig m, Member Z3 sig) => [AST] -> m AST
mkOr = func1 MkOr

mkParams :: (Carrier sig m, Member Z3 sig) => m Params
mkParams = func0 MkParams

mkStore :: (Carrier sig m, Member Z3 sig) => AST -> AST -> AST -> m AST
mkStore = func3 MkStore

mkStringSymbol :: (Carrier sig m, Member Z3 sig) => String -> m Symbol
mkStringSymbol = func1 MkStringSymbol

mkSub :: (Carrier sig m, Member Z3 sig) => [AST] -> m AST
mkSub = func1 MkSub

mkTrue :: (Carrier sig m, Member Z3 sig) => m AST
mkTrue = func0 MkTrue

mkUnaryMinus :: (Carrier sig m, Member Z3 sig) => AST -> m AST
mkUnaryMinus = func1 MkUnaryMinus

mkXor :: (Carrier sig m, Member Z3 sig) => AST -> AST -> m AST
mkXor = func2 MkXor

modelToString :: (Carrier sig m, Member Z3 sig) => Model -> m String
modelToString = func1 ModelToString

paramsSetBool :: (Carrier sig m, Member Z3 sig) => Params -> Symbol -> Bool -> m ()
paramsSetBool = func3_ ParamsSetBool

paramsSetDouble :: (Carrier sig m, Member Z3 sig) => Params -> Symbol -> Double -> m ()
paramsSetDouble = func3_ ParamsSetDouble

paramsSetSymbol :: (Carrier sig m, Member Z3 sig) => Params -> Symbol -> Symbol -> m ()
paramsSetSymbol = func3_ ParamsSetSymbol

paramsSetUInt :: (Carrier sig m, Member Z3 sig) => Params -> Symbol -> Word -> m ()
paramsSetUInt = func3_ ParamsSetUInt

paramsToString :: (Carrier sig m, Member Z3 sig) => Params -> m String
paramsToString = func1 ParamsToString

simplify :: (Carrier sig m, Member Z3 sig) => AST -> m AST
simplify = func1 Simplify

solverCheck :: (Carrier sig m, Member Z3 sig) => m Result
solverCheck = func0 SolverCheck

solverAssertCnstr :: (Carrier sig m, Member Z3 sig) => AST -> m ()
solverAssertCnstr = func1_ SolverAssertCnstr

solverGetModel :: (Carrier sig m, Member Z3 sig) => m Model
solverGetModel = func0 SolverGetModel


--------------------------------------------------------------------------------


func0 :: (Carrier sig m, Member Z3 sig) => ((a -> m a) -> Z3 m (m a)) -> m a
func1 :: (Carrier sig m, Member Z3 sig) => (a -> (b -> m b) -> Z3 m (m b)) -> a -> m b
func2 :: (Carrier sig m, Member Z3 sig) => (a -> b -> (c -> m c) -> Z3 m (m c)) -> a -> b -> m c
func3 :: (Carrier sig m, Member Z3 sig) => (a -> b -> c -> (d -> m d) -> Z3 m (m d)) -> a -> b -> c -> m d
func6 :: (Carrier sig m, Member Z3 sig) => (a -> b -> c -> d -> e -> f -> (g -> m g) -> Z3 m (m g)) -> a -> b -> c -> d -> e -> f -> m g

func1_ :: (Carrier sig m, Member Z3 sig) => (a -> m () -> Z3 m (m ())) -> a -> m ()
func2_ :: (Carrier sig m, Member Z3 sig) => (a -> b -> m () -> Z3 m (m ())) -> a -> b -> m ()
func3_ :: (Carrier sig m, Member Z3 sig) => (a -> b -> c -> m () -> Z3 m (m ())) -> a -> b -> c -> m ()

func0 f             = send (f             pure)
func1 f a           = send (f a           pure)
func2 f a b         = send (f a b         pure)
func3 f a b c       = send (f a b c       pure)
func6 f a b c d e g = send (f a b c d e g pure)

func1_ f a     = send (f a     (pure ()))
func2_ f a b   = send (f a b   (pure ()))
func3_ f a b c = send (f a b c (pure ()))


--------------------------------------------------------------------------------
-- Carrier
--------------------------------------------------------------------------------

newtype Z3C (m :: Type -> Type) (a :: Type)
  = Z3C { unZ3C :: ReaderC Env m a }
  deriving newtype (Applicative, Functor, Monad, MonadIO)

instance
     ( Carrier sig m
     , Member (Error Z3Error) sig
     , MonadIO m
     ) => Carrier (Z3 :+: sig) (Z3C m) where
  eff :: (Z3 :+: sig) (Z3C m) (Z3C m a) -> Z3C m a
  eff = \case
    L z3 ->
      Z3C (ReaderC (\env -> handleZ3 env z3 >>= runReader env . unZ3C))

    R other ->
      Z3C (eff (R (handleCoercible other)))

handleZ3 ::
     ( Carrier sig m
     , Member (Error Z3Error) sig
     , MonadIO m
     )
  => Env
  -> Z3 (Z3C m) a
  -> m a
handleZ3 (Env ctx solver) = \case
  AddConstInterp             a b c       k -> wrap3 a b c       (const k) Z3.addConstInterp
  AddFuncInterp              a b c       k -> wrap3 a b c              k  Z3.addFuncInterp
  AndThenTactic              a b         k -> wrap2 a b                k  Z3.andThenTactic
  AppToAst                   a           k -> wrap1 a                  k  Z3.appToAst
  ApplyTactic                a b         k -> wrap2 a b                k  Z3.applyTactic
  AstToString                a           k -> wrap1 a                  k  Z3.astToString
  BenchmarkToSMTLibString    a b c d e f k -> wrap6 a b c d e f        k  Z3.benchmarkToSMTLibString
  FixedpointAddRule          a b c       k -> wrap3 a b c       (const k) Z3.fixedpointAddRule
  FixedpointGetAnswer        a           k -> wrap1 a                  k  Z3.fixedpointGetAnswer
  FixedpointGetAssertions    a           k -> wrap1 a                  k  Z3.fixedpointGetAssertions
  FixedpointPop              a           k -> wrap1 a           (const k) Z3.fixedpointPop
  FixedpointPush             a           k -> wrap1 a           (const k) Z3.fixedpointPush
  FixedpointQueryRelations   a b         k -> wrap2 a b                k  Z3.fixedpointQueryRelations
  FixedpointRegisterRelation a b         k -> wrap2 a b         (const k) Z3.fixedpointRegisterRelation
  FixedpointSetParams        a b         k -> wrap2 a b         (const k) Z3.fixedpointSetParams
  FuncDeclToString           a           k -> wrap1 a                  k  Z3.funcDeclToString
  FuncEntryGetArg            a b         k -> wrap2 a b                k  Z3.funcEntryGetArg
  FuncEntryGetNumArgs        a           k -> wrap1 a                  k  Z3.funcEntryGetNumArgs
  FuncEntryGetValue          a           k -> wrap1 a                  k  Z3.funcEntryGetValue
  FuncInterpGetArity         a           k -> wrap1 a                  k  Z3.funcInterpGetArity
  FuncInterpGetElse          a           k -> wrap1 a                  k  Z3.funcInterpGetElse
  FuncInterpGetEntry         a b         k -> wrap2 a b                k  Z3.funcInterpGetEntry
  FuncInterpGetNumEntries    a           k -> wrap1 a                  k  Z3.funcInterpGetNumEntries
  GetAppArg                  a b         k -> wrap2 a b                k  Z3.getAppArg
  GetAppDecl                 a           k -> wrap1 a                  k  Z3.getAppDecl
  GetAppNumArgs              a           k -> wrap1 a                  k  Z3.getAppNumArgs
  GetApplyResultNumSubgoals  a           k -> wrap1 a                  k  Z3.getApplyResultNumSubgoals
  GetApplyResultSubgoal      a b         k -> wrap2 a b                k  Z3.getApplyResultSubgoal
  GetArity                   a           k -> wrap1 a                  k  Z3.getArity
  GetArraySortDomain         a           k -> wrap1 a                  k  Z3.getArraySortDomain
  GetArraySortRange          a           k -> wrap1 a                  k  Z3.getArraySortRange
  GetAsArrayFuncDecl         a           k -> wrap1 a                  k  Z3.getAsArrayFuncDecl
  GetAstKind                 a           k -> wrap1 a                  k  Z3.getAstKind
  GetBoolValue               a           k -> wrap1 a                  k  Z3.getBoolValue
  GetBvSortSize              a           k -> wrap1 a                  k  Z3.getBvSortSize
  GetConstDecl               a b         k -> wrap2 a b                k  Z3.getConstDecl
  GetConstInterp             a b         k -> wrap2 a b                k  Z3.getConstInterp
  MkAdd                      a           k -> wrap1 a                  k  Z3.mkAdd
  MkAnd                      a           k -> wrap1 a                  k  Z3.mkAnd
  MkApp                      a b         k -> wrap2 a b                k  Z3.mkApp
  MkArraySort                a b         k -> wrap2 a b                k  Z3.mkArraySort
  MkBoolSort                             k -> wrap0                    k  Z3.mkBoolSort
  MkDistinct                 a           k -> wrap1 a                  k  Z3.mkDistinct
  MkEq                       a b         k -> wrap2 a b                k  Z3.mkEq
  MkFalse                                k -> wrap0                    k  Z3.mkFalse
  MkFuncDecl                 a b c       k -> wrap3 a b c              k  Z3.mkFuncDecl
  MkGe                       a b         k -> wrap2 a b                k  Z3.mkGe
  MkGt                       a b         k -> wrap2 a b                k  Z3.mkGt
  MkIff                      a b         k -> wrap2 a b                k  Z3.mkIff
  MkImplies                  a b         k -> wrap2 a b                k  Z3.mkImplies
  MkIntSort                              k -> wrap0                    k  Z3.mkIntSort
  MkInteger                  a           k -> wrap1 a                  k  Z3.mkInteger
  MkIntSymbol                a           k -> wrap1 a                  k  Z3.mkIntSymbol
  MkIte                      a b c       k -> wrap3 a b c              k  Z3.mkIte
  MkLe                       a b         k -> wrap2 a b                k  Z3.mkLe
  MkLt                       a b         k -> wrap2 a b                k  Z3.mkLt
  MkMul                      a           k -> wrap1 a                  k  Z3.mkMul
  MkNot                      a           k -> wrap1 a                  k  Z3.mkNot
  MkOr                       a           k -> wrap1 a                  k  Z3.mkOr
  MkParams                               k -> wrap0                    k  Z3.mkParams
  MkSolver                               k -> wrap0                    k  Z3.mkSolver
  MkStore                    a b c       k -> wrap3 a b c              k  Z3.mkStore
  MkStringSymbol             a           k -> wrap1 a                  k  Z3.mkStringSymbol
  MkSub                      a           k -> wrap1 a                  k  Z3.mkSub
  MkTrue                                 k -> wrap0                    k  Z3.mkTrue
  MkUnaryMinus               a           k -> wrap1 a                  k  Z3.mkUnaryMinus
  MkXor                      a b         k -> wrap2 a b                k  Z3.mkXor
  ModelToString              a           k -> wrap1 a                  k  Z3.modelToString
  ParamsSetBool              a b c       k -> wrap3 a b c       (const k) Z3.paramsSetBool
  ParamsSetDouble            a b c       k -> wrap3 a b c       (const k) Z3.paramsSetDouble
  ParamsSetSymbol            a b c       k -> wrap3 a b c       (const k) Z3.paramsSetSymbol
  ParamsSetUInt              a b c       k -> wrap3 a b c       (const k) Z3.paramsSetUInt
  ParamsToString             a           k -> wrap1 a                  k  Z3.paramsToString
  Simplify                   a           k -> wrap1 a                  k  Z3.simplify

  SolverAssertCnstr a k -> wrap2 solver a (const k) Z3.solverAssertCnstr
  SolverCheck         k -> wrap1 solver          k  Z3.solverCheck
  SolverGetModel      k -> wrap1 solver          k  Z3.solverGetModel

  where
    wrap0 :: (Carrier sig m, Member (Error Z3Error) sig, MonadIO m) => (a -> b) -> (Context -> IO a) -> m b
    wrap1 :: (Carrier sig m, Member (Error Z3Error) sig, MonadIO m) => a -> (b -> c) -> (Context -> a -> IO b) -> m c
    wrap2 :: (Carrier sig m, Member (Error Z3Error) sig, MonadIO m) => a -> b -> (c -> d) -> (Context -> a -> b -> IO c) -> m d
    wrap3 :: (Carrier sig m, Member (Error Z3Error) sig, MonadIO m) => a -> b -> c -> (d -> e) -> (Context -> a -> b -> c -> IO d) -> m e
    wrap6 :: (Carrier sig m, Member (Error Z3Error) sig, MonadIO m) => a -> b -> c -> d -> e -> f -> (g -> h) -> (Context -> a -> b -> c -> d -> e -> f -> IO g) -> m h

    wrap0             k f = sendZ3 (f ctx)             k
    wrap1 a           k f = sendZ3 (f ctx a)           k
    wrap2 a b         k f = sendZ3 (f ctx a b)         k
    wrap3 a b c       k f = sendZ3 (f ctx a b c)       k
    wrap6 a b c d e g k f = sendZ3 (f ctx a b c d e g) k

    sendZ3 ::
          ( Carrier sig m
          , Member (Error Z3Error) sig
          , MonadIO m
          )
       => IO a
       -> (a -> b)
       -> m b
    sendZ3 m k =
      liftIO (tryZ3 m) >>=
        either throwError (pure . k)

    tryZ3 :: IO a -> IO (Either Z3Error a)
    tryZ3 = try

data Env
  = Env
  { envContext :: Context
  , envSolver :: Solver
  }


runZ3 ::
     ( Carrier sig m
     , Member (Error Z3Error) sig
     , MonadIO m
     )
  => Z3C m a
  -> m a
runZ3 action = do
  ctx :: Context <-
    liftIO (withConfig mkContext)

  solver :: Solver <-
    liftIO (mkSolver ctx)

  runReaderC (unZ3C action) Env
    { envContext = ctx
    , envSolver = solver
    }
