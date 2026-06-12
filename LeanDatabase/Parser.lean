import Lean
import Mathlib
import LeanDatabase.Schema
import LeanDatabase.SQLToolbox

open Lean Meta Elab Term

namespace LeanDatabase

/--
# Parser for SQL-like filter expressions

Since SQL types are all Lean constants, we represent them by names.
-/
def elabFilter' (schema : List (Name × Name)) (stx : Syntax) : TermElabM Expr := do
  match schema with
  | [] => elabTermEnsuringType stx (mkConst ``Bool)
  | (name, colType) :: rest => do
    let colTypeExpr ←  Term.mkConst colType
    withLocalDeclD name colTypeExpr fun localVar => do
      let restExpr ← elabFilter' rest stx
      mkLambdaFVars #[localVar] restExpr

inductive SQLTypeProxy where
  | int
  | bool
  | float
  | string
deriving Repr, DecidableEq, ToExpr


@[reducible]
def SQLTypeProxy.type : SQLTypeProxy → Type
  | .int => Int
  | .bool => Bool
  | .float => Rat
  | .string => String

instance (t : SQLTypeProxy) : DecidableEq t.type :=
  match t with
  | .int => inferInstance
  | .bool => inferInstance
  | .float => inferInstance
  | .string => inferInstance

def typeExpr (t : SQLTypeProxy) : Expr :=
  match t with
  | .int => mkConst ``Int
  | .bool => mkConst ``Bool
  | .float => mkConst ``Rat
  | .string => mkConst ``String

def sqlProxy (sqlType : String) : SQLTypeProxy :=
  let s := sqlType.toLower
  if s.startsWith "varchar" then .string
  else if s.startsWith "int" then .int
  else if s.startsWith "bool" then .bool
  else if s.startsWith "float" then .float
  else if s.startsWith "text" then .string
  else if s.startsWith "char" then .string
  else .string -- default to string for unrecognized types

def elabFilter (schema : List (Name × SQLTypeProxy)) (stx : Syntax) : TermElabM Expr := do
  match schema with
  | [] => elabTermEnsuringType stx (mkConst ``Bool)
  | (name, colType) :: rest => do
    let colTypeExpr := typeExpr colType
    withLocalDeclD name colTypeExpr fun localVar => do
      let restExpr ← elabFilter rest stx
      mkLambdaFVars #[localVar] restExpr

@[reducible]
def colTypeOfList (l: List SQLTypeProxy) : Fin l.length → Type :=
  fun i => (l.get i).type

instance sqlTypeDecEq (l: List SQLTypeProxy) : (i : Fin l.length) → DecidableEq (colTypeOfList l i) := by
  match l with
  | [] =>
    intro ⟨i, hi⟩
    simp at hi
  | t :: rest =>
    intro ⟨i, hi⟩
    match i with
    | 0 => exact inferInstance
    | j+1 =>
      exact sqlTypeDecEq rest ⟨j, by simp at hi; assumption⟩

-- Testing that decidable equality works for the generated types
example (l: List SQLTypeProxy) : TypedRelation (colTypeOfList l) :=
  emptyRel (fun _ => "dummy")

@[reducible]
def TypedRelationOfList (l: List SQLTypeProxy) : Type :=
  TypedRelation (colTypeOfList l)

def sqlTypeListExpr (l: List SQLTypeProxy) : MetaM Expr := do
  match l with
  | [] => mkAppOptM ``List.nil #[mkConst ``SQLTypeProxy]
  | t :: rest =>
    mkAppM ``List.cons #[toExpr t, ← sqlTypeListExpr rest]

-- #check List.nil
-- #check mkAppOptM
-- #check TypedRelationOfList

def parseFilter (schemaStr : List (String × String)) (str : String) : TermElabM Expr := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term str | throwError "Failed to parse filter expression: {str}"
  let schema := schemaStr.map (fun (name, colType) => (name.toName, sqlProxy colType))
  elabFilter schema stx

def elabTypeRelMap (schema : List (Name × SQLTypeProxy)) (stx: Syntax) : TermElabM Expr := do
  let colTypes := schema.map (fun (_, colType) => colType)
  let listExpr ← sqlTypeListExpr colTypes
  let type ← mkAppM ``TypedRelationOfList #[listExpr]
  let filter ← elabFilter schema stx
  withLocalDeclD `typedRel type fun typeRel => do
    let restExpr ← mkAppM ``restrictionCurried #[typeRel, filter]
    mkLambdaFVars #[typeRel] restExpr

def parseTypeRelMap  (schemaStr : List (String × String)) (str : String) : TermElabM Expr := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term str | throwError "Failed to parse filter expression: {str}"
  let schema := schemaStr.map (fun (name, colType) => (name.toName, sqlProxy colType))
  elabTypeRelMap schema stx

def egFilter := parseFilter [("age", "Int"), ("isActive", "Bool")] "age > 30 && isActive"

def egTypeRelMap := parseTypeRelMap [("age", "Int"), ("isActive", "Bool")] "age > 30 && isActive"

-- #check egTypeRelMap

elab "egfilter%" : term => do
  let e ← egFilter
  return e

elab "egTypeRelMap%" : term => do
  let e ← egTypeRelMap
  return e

-- #check egTypeRelMap%

-- #check egfilter%

-- #eval egfilter% 32 true

example : egfilter% = fun age isActive ↦ (31 ≤  age) && isActive && (20 < age)  := by
  grind

def egFilter' := parseFilter [("age", "Int"), ("isActive", "Bool")] "age > 30"

def egTypeRelMap' := parseTypeRelMap [("age", "Int"), ("isActive", "Bool")] "age > 30 && isActive && age > 20"

elab "egfilter%%" : term => do
  let e ← egFilter'
  return e

elab "egTypeRelMap%%" : term => do
  let e ← egTypeRelMap'
  return e

-- #check egfilter%%

-- #eval egfilter%% 32 true

-- #check egTypeRelMap%%

def eg1 := egTypeRelMap%
def eg2 := egTypeRelMap%%

example : eg1 = eg2 := by
  grind +locals

example : egTypeRelMap% = egTypeRelMap%% := by
  grind +locals

def checkEquiv (data: Json) : TermElabM Bool := do
    let .ok schema := data.getObjValAs? (List Json) "schema" | throwError "Missing schema"
    let schemaStr : List (String × String) ←  schema.mapM fun colJson => do
      let .ok name := colJson.getObjValAs? String "name" | throwError "Missing column name"
      let .ok sqlType := colJson.getObjValAs? String "type" | throwError "Missing column type"
      pure (name, sqlType)
    let .ok firstStr := data.getObjValAs? String "first" | throwError "Missing first expression"
    let .ok secondStr := data.getObjValAs? String "second" | throwError "Missing second expression"
    let firstExpr ← parseFilter schemaStr firstStr
    let secondExpr ← parseFilter schemaStr secondStr
    let goalType ←  mkEq firstExpr secondExpr
    -- logInfo m!"Checking equivalence of:\n  {firstStr}\n  {secondStr}\nParsed as:\n  {← ppExpr firstExpr}\n  {← ppExpr secondExpr}; Goal: {← ppExpr goalType}"
    let mvar ← mkFreshExprMVar goalType
    let tac ← `(tacticSeq| grind)
    try
        let (goals, _) ← Elab.runTactic mvar.mvarId! tac
        pure goals.isEmpty
    catch _ =>
        -- logInfo m!"Error occurred while running tactic: {e.toMessageData}"
        pure false

def checkEquivCore (data: Json) : CoreM Bool := do
    let res :=  checkEquiv data |>.run' {} |>.run' {}
    res

macro "SELECT" " * " "FROM" ident "WHERE" t:term : term =>
    return t

macro:30 t:term "AND" s:term : term =>
  `($t && $s)

macro:30 t:term "OR" s:term : term =>
  `($t || $s)

macro:85 "NOT" t:term : term =>
  `(!$t)

def dataEg := json% {"schema": [{"name": "age", "type": "Int"}, {"name": "isActive", "type": "Bool"}],
  "first": "SELECT * FROM table WHERE age > 30 AND isActive","second": "SELECT * FROM table WHERE age > 30 && isActive && age > 20"}

-- #eval checkEquiv dataEg


end LeanDatabase
