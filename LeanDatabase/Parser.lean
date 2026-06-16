import Lean
import Mathlib
import LeanDatabase.Schema
import LeanDatabase.SQLToolbox
import LeanDatabase.Operators.CrossProduct

open Lean Meta Elab Term

namespace LeanDatabase

/-!
# Parser for SQL-like filter expressions

-/

declare_syntax_cat sql_query
declare_syntax_cat sql_from
declare_syntax_cat sql_cols
syntax "*" : sql_cols
declare_syntax_cat sql_col
syntax ident : sql_col
syntax term "AS" ident : sql_col
syntax sql_col,* : sql_cols


-- Base Cases (The atomic sources of data)
syntax ident : sql_from                               -- 1. Standard table name
syntax "(" sql_query ")" "AS" ident : sql_from       -- 2. Subquery with mandatory alias

-- Recursive Cases (Chaining joins from left to right)
syntax sql_from "JOIN" ident "ON" term : sql_from     -- 3. Explicit Inner Join
syntax sql_from "CROSS" "JOIN" ident : sql_from       -- 4. Cross Join
syntax sql_from "," sql_from : sql_from              -- 5. Comma-separated (Cartesian Product)

syntax "SELECT" sql_cols "FROM" sql_from ("WHERE" term)? (";")? : sql_query

macro_rules -- Gemini generated (then fixed) rules for desugaring JOINs and CROSS JOINs into comma-separated FROM clauses with WHERE conditions; GROUP BY omitted for now.
  -----------------------------------------------------------------------------
  -- CASE A: The query ALREADY has an existing WHERE clause
  -----------------------------------------------------------------------------
  -- 1. Desugar INNER JOIN -> Replace with comma, append condition via AND

  | `(sql_query| SELECT $items FROM $f:sql_from JOIN $tNext:ident ON $onCond WHERE $whereCond ;) =>
      `(sql_query| SELECT $items FROM $f, $tNext:ident WHERE $whereCond AND $onCond;)

  -- 2. Desugar CROSS JOIN -> Replace with comma, leave WHERE unchanged

  | `(sql_query| SELECT $items FROM $f:sql_from CROSS JOIN $tNext:ident WHERE $whereCond ;) =>
      `(sql_query| SELECT $items FROM $f, $tNext:ident WHERE $whereCond ;)

  -----------------------------------------------------------------------------
  -- CASE B: The query does NOT have a WHERE clause yet
  -----------------------------------------------------------------------------
  -- 3. Desugar INNER JOIN -> Initialize the WHERE clause with the ON condition

  | `(sql_query| SELECT $items FROM $f:sql_from JOIN $tNext:ident ON $onCond;) =>
      `(sql_query| SELECT $items FROM $f, $tNext:ident WHERE $onCond ;)

  -- 4. Desugar CROSS JOIN -> Replace with comma, no WHERE clause needed

  | `(sql_query| SELECT $items FROM $f:sql_from CROSS JOIN $tNext:ident;) =>
      `(sql_query| SELECT $items FROM $f, $tNext:ident;)


partial def getIdents (stx : TSyntax `sql_from) : List Name :=
  match stx with
  | `(sql_from| $db:ident) => [db.getId]
  | `(sql_from| $f1:sql_from , $f2:sql_from) => getIdents f1 ++ getIdents f2
  | _ => []

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
  else if s.startsWith "double" then .float
  else if s.startsWith "real" then .float
  else if s.startsWith "number" then .int
  else if s.startsWith "numeric" then .int
  else if s.startsWith "decimal" then .int
  else if s.startsWith "bigint" then .int
  else if s.startsWith "smallint" then .int
  else if s.startsWith "text" then .string
  else if s.startsWith "char" then .string
  else if s.startsWith "date" then .string
  else if s.startsWith "timestamp" then .string
  else .string -- default to string for unrecognized types


def withLetColumnVars (schemaName: Name) (schema : List ((Name × SQLTypeProxy) × Expr)) (typedTupleVar : Expr)  (k : α →  TermElabM Expr) (x : α) : TermElabM Expr := do
  match schema with
  | [] => k x
  | ((name, colType), projExpr) :: rest => do
    let colTypeExpr := typeExpr colType
    let fullName := schemaName ++ name
    let funcName := fullName ++ `proj
    let relType ← inferType typedTupleVar
    let funcType ← mkArrow relType colTypeExpr
    withLetDecl funcName funcType projExpr fun funcVar => do
      let colExpr ← mkAppM' funcVar #[typedTupleVar]
      let colExpr ← reduce colExpr
      withLetDecl fullName colTypeExpr colExpr fun localVar => do
        withLetDecl name colTypeExpr localVar fun localVar' => do
          let restExpr ← withLetColumnVars schemaName rest typedTupleVar k x
          mkLetFVars #[funcVar, localVar, localVar'] restExpr

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
def TypedTupleOfList (l: List SQLTypeProxy) : Type :=
  TypedTuple (colTypeOfList l)

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
-- #check TypedTupleOfList


def withSchemasTupleVars (schemas : List (Name × List (Name × SQLTypeProxy)))  (k : α →  TermElabM Expr) (x : α) : TermElabM Expr := do
  match schemas with
  | [] => k x
  | (schemaName, schema) :: rest => do
    let colTypes := schema.map (fun (_, colType) => colType)
    let listExpr ← sqlTypeListExpr colTypes
    let type ← mkAppM ``TypedTupleOfList #[listExpr]
    let colExprs ← List.finRange colTypes.length |>.mapM fun i => do
        let index := toExpr i
        withLocalDeclD `typedTuple type fun typedTuple => do
          let value ← mkAppM' typedTuple #[index]
          mkLambdaFVars #[typedTuple] value
    let schemaExprs := schema.zip colExprs
    withLocalDeclD (schemaName ++ `coords) type fun typedTuple => do
      let inner ← withLetColumnVars schemaName schemaExprs typedTuple (withSchemasTupleVars rest k) x
      mkLambdaFVars #[typedTuple] inner

def withSchemasRelVars (schemas : List (Name × List (Name × SQLTypeProxy)))  (k : List (Expr × Name × List (Name × SQLTypeProxy)) →  TermElabM α)  : TermElabM α := do
  match schemas with
  | [] => k []
  | (schemaName, schema) :: rest => do
    let colTypes := schema.map (fun (_, colType) => colType)
    let listExpr ← sqlTypeListExpr colTypes
    let type ← mkAppM ``TypedRelationOfList #[listExpr]
    withLocalDeclD schemaName type fun typedRel => do
      withSchemasRelVars rest ((fun l ↦ k ((typedRel, schemaName, schema) :: l)))

-- #eval List.finRange 3

-- This is the "WHERE" part of a SQL query, which is a function from a TypedRelation to a TypedRelation. This is to be applied to the database, which may be a single schema or built from multiple schemas.
def elabTypedTupleFilter (schemaName : Name) (schema : List (Name × SQLTypeProxy)) (stx: Syntax) : TermElabM Expr := do
  withSchemasTupleVars [(schemaName, schema)] (fun stx => elabTermEnsuringType stx (mkConst ``Bool)) stx

def parseTypedTupleFilter  (schemaStr : List (String × String)) (str : String) : TermElabM Expr := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term str | throwError "Failed to parse filter expression: {str}"
  let schema := schemaStr.map (fun (name, colType) => (name.toName, sqlProxy colType))
  elabTypedTupleFilter `schema schema stx

-- #check selection

def elabTypedRelMap (schemas : List (Name × List (Name × SQLTypeProxy))) (stx: Syntax) : TermElabM Expr := do
  withSchemasRelVars schemas fun relVars => do
    let [(relVar, _)] := relVars | throwError "Expected exactly one relation variable"
    let [(schemaName, schema)] := schemas | throwError "Expected exactly one schema"
    let filter ← elabTypedTupleFilter schemaName schema stx
    -- logInfo m!"Elaborated filter type: {← ppExpr <| ← inferType filter}"
    let e ← mkAppM ``selection #[filter, relVar]
    let vars := relVars.map (fun (relVar, _, _) => relVar)
    mkLambdaFVars vars.toArray e
  -- logInfo m!"Elaborated relation map type: {← ppExpr <| ← inferType outer}"

def parseTypedRelMap  (schemasStr : List (String × List (String × String))) (str : String) : TermElabM Expr := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term str | throwError "Failed to parse filter expression: {str}"
  let schemas := schemasStr.map (fun (schemaName, schema) =>
    let schema' := schema.map (fun (name, colType) => (name.toName, sqlProxy colType))
    (schemaName.toName, schema'))
  elabTypedRelMap schemas stx

section product

variable {n m : Nat}
variable {colType1 : Fin n → Type} [∀ i, DecidableEq (colType1 i)]
variable {colType2 : Fin m → Type} [∀ i, DecidableEq (colType2 i)]

abbrev colTypeOfProduct (colType1: Fin n → Type) (colType2: Fin m → Type) : Fin (n + m) →  Type :=
  fun ⟨i, h⟩ =>
    if h : i < n then
      colType1 ⟨i, h⟩
    else
      colType2 ⟨i - n, by grind⟩

def prodTypedTuple (t1 : TypedTuple colType1) (t2 : TypedTuple colType2) :
    TypedTuple (colTypeOfProduct colType1 colType2) := fun ⟨i, h⟩ => by
  if h : i < n then
    simp [colTypeOfProduct, h]
    exact t1 ⟨i, h⟩
  else
    simp [colTypeOfProduct, h]
    exact t2 ⟨i - n, by grind⟩

def leftProj (t : TypedTuple (colTypeOfProduct colType1 colType2)) : TypedTuple colType1 := fun ⟨i, h⟩ => by
 let t' := t ⟨i, by grind⟩
 simp [colTypeOfProduct, h] at t'
 exact t'

def rightProj (t : TypedTuple (colTypeOfProduct colType1 colType2)) : TypedTuple colType2 := fun ⟨i, h⟩ => by
 let t' := t ⟨i + n, by grind⟩
 simp [colTypeOfProduct] at t'
 exact t'


end product

/--
This is the main entry point for parsing a full SQL query, which includes the "SELECT", "FROM", and "WHERE" clauses. For simplicity, we only handle "SELECT *" and a single table in the "FROM" clause, but this can be extended in the future. The output is an expression representing the filter to be applied to the database, along with the schema of the table returned.
-/
def elabSqlQuery (schemas : List (Name × List (Name × SQLTypeProxy))) (stx: Syntax) :
    TermElabM (Expr × List (Name × SQLTypeProxy)) := do
  let stx ← liftMacroM <| expandMacros stx
  match stx with
  | `(sql_query| SELECT * FROM $db:ident WHERE $filter;) => do
    let .some (schemaName, schema) := schemas.findSome? (fun (name, schema) => if name == db.getId then some (name, schema) else none) | throwError s!"Unknown table {db}"
    let filterExpr ← elabTypedRelMap [(schemaName, schema)] filter
    pure (filterExpr, schema)
  | `(sql_query| SELECT * FROM $dbs:sql_from;) => do
    let selectedDbs := getIdents dbs
    let selectedSchemas ←  selectedDbs.mapM fun db => do
      let .some (schemaName, schema) :=
      schemas.findSome? (fun (name, schema) => if name == db then some (name, schema) else none) | throwError s!"Unknown table {db}"
      pure (schemaName, schema)
    let productRel ← withSchemasRelVars selectedSchemas fun relVars => do
      let (head, name, _) :: tail := relVars | throwError "Expected at least one table in FROM clause"
      let tail := tail.map (fun (relVar, _) => relVar)
      tail.foldlM (fun rel acc => do
        let combinedRel ← mkAppM ``crossProductRel #[acc, rel, toExpr name.toString, toExpr "tail"]
        reduce combinedRel) head
    let combinedSchema := selectedSchemas.foldl (fun acc (_, schema) => acc ++ schema) []
    pure (productRel, combinedSchema)
  | _ => throwError "Unexpected syntax for SQL query"

-- Examples

def egTypedTupleFilter := parseTypedTupleFilter [("age", "Int"), ("isActive", "Bool")] "age > 30 && isActive"

def egTypedTupleFilter' := parseTypedTupleFilter [("age", "Int"), ("isActive", "Bool")] "age > 30 && isActive && age > 20"

def egTypedRelMap := parseTypedRelMap [("schema", [("age", "Int"), ("isActive", "Bool")])] "age > 30 && isActive"

def egTypedRelMap' := parseTypedRelMap [("schema", [("age", "Int"), ("isActive", "Bool")])] "age > 30 && isActive && age > 20"

elab "egTypedTupleFilter%" : term => do
  let e ← egTypedTupleFilter
  return e

elab "egTypedTupleFilter%%" : term => do
  let e ← egTypedTupleFilter'
  return e

elab "egTypedRelMap%" : term => do
  let e ← egTypedRelMap
  return e

elab "egTypedRelMap%%" : term => do
  let e ← egTypedRelMap'
  return e

-- #check egTypedRelMap%

-- #check egTypedTupleFilter%%

def eg1 := egTypedTupleFilter%
def eg2 := egTypedTupleFilter%%

example : eg1 = eg2 := by
  grind only [eg1, eg2, #2ec2, #99da]

set_option pp.funBinderTypes true in
example : egTypedTupleFilter% = egTypedTupleFilter%% := by
  grind

set_option pp.funBinderTypes true in
example : egTypedRelMap% = egTypedRelMap%% := by
  grind

def checkEquiv (data: Json) : TermElabM Bool := do
    let .ok schema := data.getObjValAs? (List Json) "schema" | throwError "Missing schema"
    let schemaStr : List (String × String) ←  schema.mapM fun colJson => do
      let .ok name := colJson.getObjValAs? String "name" | throwError "Missing column name"
      let .ok sqlType := colJson.getObjValAs? String "type" | throwError "Missing column type"
      pure (name, sqlType)
    let .ok firstStr := data.getObjValAs? String "first" | throwError "Missing first expression"
    let .ok secondStr := data.getObjValAs? String "second" | throwError "Missing second expression"
    let firstExpr ← parseTypedTupleFilter schemaStr firstStr
    let secondExpr ← parseTypedTupleFilter schemaStr secondStr
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

-- Test for macro expansion

declare_syntax_cat blah

syntax "Hi" : blah
syntax "Hello" : blah
syntax blah "," blah : blah

macro_rules
  | `(blah| Hi) => `(blah| Hello)


partial def coutHellos : TSyntax `blah → TermElabM Nat := fun stx => do
  let stx ← liftMacroM <| expandMacros stx
  match stx with
  | `(blah| Hello) => do
    return 1
  | `(blah| $x:blah , $y:blah) => do
    let n1 ← coutHellos x
    let n2 ← coutHellos y
    return n1 + n2
  | _ => throwError "Unexpected syntax"

def testHi : TermElabM Nat := do
  let stx ← `(blah| Hi)
  let n ← coutHellos stx
  return n

#eval testHi
