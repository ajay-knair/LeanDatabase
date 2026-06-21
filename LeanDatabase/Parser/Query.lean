import LeanDatabase.Parser.Context
import LeanDatabase.Operators.CrossProduct

/-!
# Top-level query parsing

`parseTypedTupleFilter` / `parseTypedRelFilter` parse a `WHERE`-predicate string against a schema;
`elabSqlQuery` is the full `SELECT … FROM … WHERE …` entry point that dispatches on query shape and
composes the per-operator elaborators (`Parser.Context`) with the cross-product operator.
-/

open Lean Meta Elab Term

namespace LeanDatabase

def parseTypedTupleFilter  (schemaStr : List (String × String)) (str : String) : TermElabM Expr := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term str | throwError "Failed to parse filter expression: {str}"
  let schema := schemaStr.map (fun (name, colType) => (name.toName, sqlProxy colType))
  let schema := schemaWithFullNames `schema schema
  let labels := schema.map (fun (name, _) => name)
  let stx ← expandNames labels stx
  elabTypedTupleFilter [(`schema, schema)] stx

def parseTypedRelFilter  (schemasStr : List (String × List (String × String))) (str : String) : TermElabM Expr := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term str | throwError "Failed to parse filter expression: {str}"
  let schemas := schemasStr.map (fun (schemaName, schema) =>
    let schema' := schema.map (fun (name, colType) => (name.toName, sqlProxy colType))
    (schemaName.toName, schema'))
  let schemas := schemas.map (fun (schemaName, schema) => (schemaName, schemaWithFullNames schemaName schema))
  let labels := schemas.foldl (fun acc (_, schema) => acc ++ schema.map (fun (name, _) => name)) []
  let stx ← expandNames labels stx
  elabTypedRelFilterSimple schemas stx

/--
This is the main entry point for parsing a full SQL query, which includes the "SELECT", "FROM", and "WHERE" clauses. For simplicity, we only handle "SELECT *" and a single table in the "FROM" clause, but this can be extended in the future. The output is an expression representing the filter to be applied to the database, along with the schema of the table returned.

This is in the context of table variables. The expressions returned can be compared for equality, containment etc. using the `sql_equiv` tactic.
-/
def elabSqlQueryCore (tableVars : List (Expr × Name × List (Name × SQLTypeProxy))) (stx: Syntax) :
    TermElabM (Expr × List (Name × SQLTypeProxy)) :=  do
  let stx ← liftMacroM <| expandMacros stx
  match stx with
  | `(sql_query| SELECT * FROM $dbs:sql_from $[;]?) => do
    let (productExpr, combinedSchema) ← productPair dbs
    let vars := tableVars.map (fun (relVar, _, _) => relVar)
    return (← mkLambdaFVars vars.toArray productExpr, combinedSchema)
  | `(sql_query| SELECT * FROM $dbs:sql_from WHERE $filter $[;]?) => do
    let (productExpr, combinedSchema) ← productPair dbs
    let filter ← elabTypedTupleFilter [(`table, combinedSchema)] filter
    let filterExpr ← mkAppM ``restriction #[filter, productExpr]
    let vars := tableVars.map (fun (relVar, _, _) => relVar)
    return (← mkLambdaFVars vars.toArray filterExpr, combinedSchema)
  | `(sql_query| SELECT $cols:sql_col,* FROM $dbs:sql_from WHERE $filter $[;]?) => do
    let (productExpr, combinedSchema) ← productPair dbs
    let filter ← elabTypedTupleFilter [(`table, combinedSchema)] filter
    let filterExpr ← mkAppM ``restriction #[filter, productExpr]
    let colStxs := cols.getElems
    let cols := colStxs.map sqlColTerm
    let names := colStxs.map sqlColName
    let nameStrs := names.map (·.toString)
    let nameExpr := toExpr nameStrs
    let (m, types) ← elabTypedTupleProjection [(`table, combinedSchema)] cols.toList
    let e' ← mkAppM ``TypedRelation.map #[m, nameExpr, filterExpr]
    let vars := tableVars.map (fun (relVar, _, _) => relVar)
    return (← mkLambdaFVars vars.toArray e', names.toList.zip types)
  | `(sql_query| SELECT $cols:sql_col,* FROM $dbs:sql_from $[;]?) => do
    let (productExpr, combinedSchema) ← productPair dbs
    let colStxs := cols.getElems
    let cols := colStxs.map sqlColTerm
    let names := colStxs.map sqlColName
    let nameStrs := names.map (·.toString)
    let nameExpr := toExpr nameStrs
    let (m, types) ← elabTypedTupleProjection [(`table, combinedSchema)] cols.toList
    let e' ← mkAppM ``TypedRelation.map #[m, nameExpr, productExpr]
    let vars := tableVars.map (fun (relVar, _, _) => relVar)
    return (← mkLambdaFVars vars.toArray e', names.toList.zip types)
  | _ => throwError "Unexpected syntax for SQL query"
  where productPair (dbs: TSyntax `sql_from) : TermElabM (Expr × List (Name × SQLTypeProxy)) := do
    let selectedTableNames := getIdents dbs
    let selectedTables ←  selectedTableNames.mapM fun db => do
      let .some (tableExpr, tableName, columns) :=
      tableVars.findSome? (fun (tableExpr, name, columns) => if name == db then some (tableExpr, name, columns) else none) | throwError s!"Unknown table {db}"
      pure (tableExpr, tableName, columns)
    let selectedTableVars := selectedTables.map (fun (tableExpr, _, _) => tableExpr)
    let headExpr :: tailExprs := selectedTableVars | throwError "Expected at least one table in FROM clause"
    let productExpr ← tailExprs.foldlM (fun acc rel => do
      let combinedRel ← mkAppM ``crossProductRel #[acc, rel]
      reduce combinedRel) headExpr
    let combinedSchema := selectedTables.foldl (fun acc (_, _, columns) => acc ++ columns) []
    return (productExpr, combinedSchema)

def elabSqlQuery (tables : List (Name × List (Name × SQLTypeProxy))) (stx: Syntax) :
    TermElabM (Expr × List (Name × SQLTypeProxy)) := withTableVars tables fun tableVars => do
  let stx ← liftMacroM <| expandMacros stx
  elabSqlQueryCore tableVars stx

def parseSqlQuery (tables : List (Name × List (Name × SQLTypeProxy))) (str : String) : TermElabM (Expr × List (Name × SQLTypeProxy)) := do
  let tables := tables.map (fun (tableName, columns) => (tableName, schemaWithFullNames tableName columns))
  let .ok stx := Parser.runParserCategory (← getEnv) `sql_query str | throwError "Failed to parse SQL query: {str}"
  let labels := tables.foldl (fun acc (_, columns) => acc ++ columns.map (fun (name, _) => name)) []
  let stx ← expandNames labels stx
  elabSqlQuery tables stx


/-! ## Smoke tests — the parser elaborates, and `grind` proves the equivalences -/

def egTypedTupleFilter := parseTypedTupleFilter [("age", "Int"), ("isActive", "Bool"), ("height", "Float")] "age > 30 && isActive"

def egTypedTupleFilter' := parseTypedTupleFilter [("age", "Int"), ("isActive", "Bool"), ("height", "Float")] "age > 30 && isActive && age > 20"

def egTypedRelFilter := parseTypedRelFilter [("table", [("age", "Int"), ("isActive", "Bool"), ("height", "Float")])] "age > 30 && isActive && height < 180"

def egTypedRelFilter' := parseTypedRelFilter [("table", [("age", "Int"), ("isActive", "Bool"), ("height", "Float")])] "age > 30 && isActive && age > 20 && height < 180"

def egSqlQuery := parseSqlQuery [(`table, [(`age, .int), (`isActive, .bool), (`height, .float)])] "SELECT * FROM table WHERE age > 30 && isActive && height < 180"


elab "egTypedTupleFilter%" : term => do
  let e ← egTypedTupleFilter
  return e

elab "egTypedTupleFilter%%" : term => do
  let e ← egTypedTupleFilter'
  return e

elab "egTypedRelFilter%" : term => do
  let e ← egTypedRelFilter
  return e

elab "egTypedRelFilter%%" : term => do
  let e ← egTypedRelFilter'
  return e

elab "egSqlQuery%" : term => do
  let (e, _) ← egSqlQuery
  return e

set_option pp.funBinderTypes true in
/--
info: fun (table : TypedRelationOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float]) ↦
  restriction
    (fun (table.coords : TypedTupleOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float]) ↦
      let table.age := table.coords ⟨0, ⋯⟩;
      let table.isActive := table.coords ⟨1, ⋯⟩;
      let table.height := table.coords ⟨2, ⋯⟩;
      decide (table.age > 30) && table.isActive && decide (table.height < 180))
    table : TypedRelationOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float] →
  TypedRelation (colTypeOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float])
-/
#guard_msgs in
#check egSqlQuery%

set_option pp.funBinderTypes true in
example : egTypedTupleFilter% = egTypedTupleFilter%% := by
  grind

set_option pp.funBinderTypes true in
example : egTypedRelFilter% = egTypedRelFilter%% := by
  grind

end LeanDatabase
