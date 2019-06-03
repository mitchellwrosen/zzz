module Z3.Effect
  ( Z3(..)
  -- , Z3.Effect.addConstInterp
  -- , Z3.Effect.addFuncInterp
  -- , Z3.Effect.andThenTactic
  -- , Z3.Effect.appToAst
  -- , Z3.Effect.applyTactic
  , Z3.Effect.astToString
  -- , Z3.Effect.benchmarkToSMTLibString
  -- , Z3.Effect.evalArray
  -- , Z3.Effect.fixedpointAddRule
  -- , Z3.Effect.fixedpointGetAnswer
  -- , Z3.Effect.fixedpointGetAssertions
  -- , Z3.Effect.fixedpointPop
  -- , Z3.Effect.fixedpointPush
  -- , Z3.Effect.fixedpointQueryRelations
  -- , Z3.Effect.fixedpointRegisterRelation
  -- , Z3.Effect.fixedpointSetParams
  -- , Z3.Effect.funcDeclToString
  -- , Z3.Effect.funcEntryGetArg
  -- , Z3.Effect.funcEntryGetNumArgs
  -- , Z3.Effect.funcEntryGetValue
  -- , Z3.Effect.funcInterpGetArity
  -- , Z3.Effect.funcInterpGetElse
  -- , Z3.Effect.funcInterpGetEntry
  -- , Z3.Effect.funcInterpGetNumEntries
  -- , Z3.Effect.getAppArg
  -- , Z3.Effect.getAppArgs
  -- , Z3.Effect.getAppDecl
  -- , Z3.Effect.getAppNumArgs
  -- , Z3.Effect.getApplyResultNumSubgoals
  -- , Z3.Effect.getApplyResultSubgoal
  -- , Z3.Effect.getApplyResultSubgoals
  -- , Z3.Effect.getArity
  -- , Z3.Effect.getArraySortDomain
  -- , Z3.Effect.getArraySortRange
  -- , Z3.Effect.getAsArrayFuncDecl
  -- , Z3.Effect.getAstKind
  -- , Z3.Effect.getBoolValue
  -- , Z3.Effect.getBvSortSize
  -- , Z3.Effect.getConstDecl
  -- , Z3.Effect.getConstInterp
  -- , Z3.Effect.getConsts
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
  -- , Z3.Effect.mkStore
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
    -- * Re-exports
  , Config
  , Context
  , Symbol
  ) where

import Control.Effect
import Control.Effect.Carrier
import Data.Kind (Type)
import Data.Text (Text)
import Z3.Base


data Z3 (m :: Type -> Type) (k :: Type)
  = AstToString AST (String -> k)
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
  | MkStringSymbol Text (Symbol -> k)
  | MkSub [AST] (AST -> k)
  | MkTrue (AST -> k)
  | MkUnaryMinus AST (AST -> k)
  | MkXor AST AST (AST -> k)
  | ModelToString Model (Text -> k)
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


astToString :: (Carrier sig m, Member Z3 sig) => AST -> m String
astToString = func1 AstToString

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

mkStringSymbol :: (Carrier sig m, Member Z3 sig) => Text -> m Symbol
mkStringSymbol = func1 MkStringSymbol

mkSub :: (Carrier sig m, Member Z3 sig) => [AST] -> m AST
mkSub = func1 MkSub

mkTrue :: (Carrier sig m, Member Z3 sig) => m AST
mkTrue = func0 MkTrue

mkUnaryMinus :: (Carrier sig m, Member Z3 sig) => AST -> m AST
mkUnaryMinus = func1 MkUnaryMinus

mkXor :: (Carrier sig m, Member Z3 sig) => AST -> AST -> m AST
mkXor = func2 MkXor

modelToString :: (Carrier sig m, Member Z3 sig) => Model -> m Text
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

func0 ::
     (Carrier sig m, Member Z3 sig)
  => ((a -> m a) -> Z3 m (m a))
  -> m a
func0 f =
  send (f pure)

func1 ::
     (Carrier sig m, Member Z3 sig)
  => (a -> (b -> m b) -> Z3 m (m b))
  -> a
  -> m b
func1 f a =
  send (f a pure)

func2 ::
     (Carrier sig m, Member Z3 sig)
  => (a -> b -> (c -> m c) -> Z3 m (m c))
  -> a
  -> b
  -> m c
func2 f a b =
  send (f a b pure)

func3 ::
     (Carrier sig m, Member Z3 sig)
  => (a -> b -> c -> (d -> m d) -> Z3 m (m d))
  -> a
  -> b
  -> c
  -> m d
func3 f a b c =
  send (f a b c pure)

func1_ ::
     (Carrier sig m, Member Z3 sig)
  => (a -> m () -> Z3 m (m ()))
  -> a
  -> m ()
func1_ f a =
  send (f a (pure ()))

func3_ ::
     (Carrier sig m, Member Z3 sig)
  => (a -> b -> c -> m () -> Z3 m (m ()))
  -> a
  -> b
  -> c
  -> m ()
func3_ f a b c =
  send (f a b c (pure ()))
