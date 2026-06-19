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
  elabTypedRelFilter schemas stx

/--
This is the main entry point for parsing a full SQL query, which includes the "SELECT", "FROM", and "WHERE" clauses. For simplicity, we only handle "SELECT *" and a single table in the "FROM" clause, but this can be extended in the future. The output is an expression representing the filter to be applied to the database, along with the schema of the table returned.
-/
def elabSqlQuery (schemas : List (Name × List (Name × SQLTypeProxy))) (stx: Syntax) :
    TermElabM (Expr × List (Name × SQLTypeProxy)) := do
  let stx ← liftMacroM <| expandMacros stx
  match stx with
  | `(sql_query| SELECT * FROM $db:ident WHERE $filter;) => do
    let .some (schemaName, schema) := schemas.findSome? (fun (name, schema) => if name == db.getId then some (name, schema) else none) | throwError s!"Unknown table {db}"
    let filterExpr ← elabTypedRelFilter [(schemaName, schema)] filter
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

/-! ## Smoke tests — the parser elaborates, and `grind` proves the equivalences -/

def egTypedTupleFilter := parseTypedTupleFilter [("age", "Int"), ("isActive", "Bool"), ("height", "Float")] "age > 30 && isActive"

def egTypedTupleFilter' := parseTypedTupleFilter [("age", "Int"), ("isActive", "Bool"), ("height", "Float")] "age > 30 && isActive && age > 20"

def egTypedRelFilter := parseTypedRelFilter [("schema", [("age", "Int"), ("isActive", "Bool"), ("height", "Float")])] "age > 30 && isActive && height < 180"

def egTypedRelFilter' := parseTypedRelFilter [("schema", [("age", "Int"), ("isActive", "Bool"), ("height", "Float")])] "age > 30 && isActive && age > 20 && height < 180"

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

set_option pp.funBinderTypes true in
example : egTypedTupleFilter% = egTypedTupleFilter%% := by
  grind

set_option pp.funBinderTypes true in
example : egTypedRelFilter% = egTypedRelFilter%% := by
  grind

end LeanDatabase
