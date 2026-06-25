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
  let stx ← escapeJoin stx
  match stx with
  | `(sql_query| SELECT $sel FROM $dbs:sql_from $[WHERE $filter?]? $[;]?) => do
    let (productExpr, combinedSchema) ← productPair dbs
    let filteredExpr ← match filter? with
      | some filter => do
        let filter ← elabTypedTupleFilter [(`table, combinedSchema)] filter
        mkAppM ``restriction #[filter, productExpr]
      | none => pure productExpr
    match sel with
    | `(sql_cols| *) => do
      let vars := tableVars.map (fun (relVar, _, _) => relVar)
      return (← mkLambdaFVars vars.toArray filteredExpr, combinedSchema)
    | `(sql_cols| $cols:sql_col,*) => do
      let colStxs := cols.getElems
      let cols := colStxs.map sqlColTerm
      let names := colStxs.map sqlColName |>.toList
      let nameStrs := names.map (·.toString)
      let (m, types) ← elabTypedTupleProjection [(`table, combinedSchema)] cols.toList
      let nameTypeExpr := toExpr <| nameStrs.zip types
      let e' ← mkAppM ``TypedRelation.mapByList #[filteredExpr, nameTypeExpr, m]
      let vars := tableVars.map (fun (relVar, _, _) => relVar)
      return (← mkLambdaFVars vars.toArray e', names.zip types)
    | _ => throwError "Unexpected syntax for SQL query"
  | `(sql_query| SELECT $cols:sql_col,* FROM $dbs:sql_from $[WHERE $filter?]?
      GROUP BY $groups:ident,* $[HAVING $having?]? $[;]?) => do
    let groupNames := groups.getElems.map (fun stx => stx.getId)
    let inGroup := fun name => groupNames.any (fun g => g == name)
    let (productExpr, combinedSchema) ← productPair dbs
    let filteredExpr ← match filter? with
      | some filter => do
        let filter ← elabTypedTupleFilter [(`table, combinedSchema)] filter
        mkAppM ``restriction #[filter, productExpr]
      | none => pure productExpr
    let colStxs := cols.getElems
    let cols := colStxs.map sqlColTerm
    let names := colStxs.map sqlColName |>.toList
    let nameStrs := names.map (·.toString)
    let (m, types) ← elabTypedTupleGroupProjection [(`table, combinedSchema)] cols.toList inGroup productExpr
    let nameTypeExpr := toExpr <| nameStrs.zip types
    let e' ← mkAppM ``TypedRelation.mapByList #[filteredExpr, nameTypeExpr, m]
    let vars := tableVars.map (fun (relVar, _, _) => relVar)
    return (← mkLambdaFVars vars.toArray e', names.zip types)
  | _ => throwError "Unexpected syntax for SQL query"
  where productPair (dbs: TSyntax `sql_from) : TermElabM (Expr × List (Name × SQLTypeProxy)) := do
    let selectedTableNames := getIdents dbs
    let selectedTables ←  selectedTableNames.mapM fun db => do
      let .some (tableExpr, tableName, columns) :=
      tableVars.findSome? (fun (tableExpr, name, columns) => if name == db then some (tableExpr, name, columns) else none) | throwError s!"Unknown table {db}"
      pure (tableExpr, tableName, columns)
    let combinedSchema := selectedTables.foldl (fun acc (_, _, columns) => acc ++ columns) []
    let selectedTableVars := selectedTables.map (fun (tableExpr, _, _) => tableExpr)
    let headExpr :: tailExprs := selectedTableVars | throwError "Expected at least one table in FROM clause: {← PrettyPrinter.ppCategory `sql_from dbs}"
    let productExpr ← tailExprs.foldlM (fun acc rel => do
      mkAppM ``TypedRelationOfList.append #[acc, rel]) headExpr
    return (productExpr, combinedSchema)


def elabSqlQuery (tables : List (Name × List (Name × SQLTypeProxy))) (stx: Syntax) :
    TermElabM (Expr × List (Name × SQLTypeProxy)) := withTableVars tables fun tableVars => do
  let stx ← escapeJoin stx
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

def egSqlQuery' := parseSqlQuery [(`table, [(`age, .int), (`isActive, .bool), (`height, .float)])] "SELECT * FROM table WHERE age > 30 && isActive && height < 180 && age > 20"

def egSqlQuery₁ := parseSqlQuery [(`table, [(`age, .int), (`isActive, .bool), (`height, .float)])] "SELECT age FROM table WHERE age > 30 && isActive && height < 180"

def egSqlQuery₂ := parseSqlQuery [(`table, [(`age, .int), (`isActive, .bool), (`height, .float)])] "SELECT age, height FROM table WHERE age > 30 && isActive && height < 180"

def egSqlQuery₃ := parseSqlQuery [(`table, [(`age, .int), (`isActive, .bool), (`height, .float)]), (`table2, [(`age, .int), (`isActive, .bool), (`height, .float)])] "SELECT * FROM table, table2  WHERE table.age > 30 && table.isActive && table.height < 180"

def egSqlQuery₄ := parseSqlQuery [(`table, [(`age, .int), (`isActive, .bool), (`height, .float)])] "SELECT 2 * age AS doubled_age FROM table WHERE age > 30 && isActive && height < 180"

def egSqlQuery₅ := parseSqlQuery [(`table, [(`age, .int), (`isActive, .bool), (`height, .float)])] "SELECT COUNT(*) AS count FROM table WHERE age > 30 && isActive && height < 180 GROUP BY age"

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

elab "egSqlQuery%%" : term => do
  let (e, _) ← egSqlQuery'
  return e

example : egSqlQuery% = egSqlQuery%% := by
  grind

elab "egSqlQuery₁" : term => do
  let (e, _) ← egSqlQuery₁
  return e

elab "egSqlQuery₂" : term => do
  let (e, _) ← egSqlQuery₂
  return e

elab "egSqlQuery₃" : term => do
  let (e, _) ← egSqlQuery₃
  return e

elab "egSqlQuery₄" : term => do
  let (e, _) ← egSqlQuery₄
  return e

elab "egSqlQuery₅" : term => do
  let (e, _) ← egSqlQuery₅
  return e

set_option pp.funBinderTypes true in
/--
info: fun (table : TypedRelationOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float]) ↦
  restriction
    (fun (table.coords : TypedTupleOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float]) ↦
      let table.age.proj :=
        fun (typedTuple : TypedTupleOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float]) ↦ typedTuple 0;
      let table.age := table.age.proj table.coords;
      let table.isActive.proj :=
        fun (typedTuple : TypedTupleOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float]) ↦ typedTuple 1;
      let table.isActive := table.isActive.proj table.coords;
      let table.height.proj :=
        fun (typedTuple : TypedTupleOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float]) ↦ typedTuple 2;
      let table.height := table.height.proj table.coords;
      decide (table.age > 30) && table.isActive && decide (table.height < 180))
    table : TypedRelationOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float] →
  TypedRelation (colTypeOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float])
-/
#guard_msgs in
#check egSqlQuery%

/--
info: @[reducible] def LeanDatabase.TypedTupleOfList : List SQLTypeProxy → Type :=
fun l ↦ TypedTuple (colTypeOfList l)
-/
#guard_msgs in
#print TypedTupleOfList

example : TypedTupleOfList [] := by
  intro ⟨i, hi⟩
  simp at hi

/--
info: fun table ↦
  (restriction
        (fun table.coords ↦
          let table.age.proj := fun typedTuple ↦ typedTuple 0;
          let table.age := table.age.proj table.coords;
          let table.isActive.proj := fun typedTuple ↦ typedTuple 1;
          let table.isActive := table.isActive.proj table.coords;
          let table.height.proj := fun typedTuple ↦ typedTuple 2;
          let table.height := table.height.proj table.coords;
          decide (table.age > 30) && table.isActive && decide (table.height < 180))
        table).mapByList
    [("table.age", SQLTypeProxy.int)] fun table.coords ↦
    let table.age.proj := fun typedTuple ↦ typedTuple 0;
    let table.age := table.age.proj table.coords;
    TypedTupleOfList.cons SQLTypeProxy.int table.age
      TypedTupleOfList.nil : TypedRelationOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float] →
  TypedRelation (colTypeOfList (List.map (fun x ↦ x.2) [("table.age", SQLTypeProxy.int)]))
-/
#guard_msgs in
#check egSqlQuery₁


/--
info: fun table ↦
  (restriction
        (fun table.coords ↦
          let table.age.proj := fun typedTuple ↦ typedTuple 0;
          let table.age := table.age.proj table.coords;
          let table.isActive.proj := fun typedTuple ↦ typedTuple 1;
          let table.isActive := table.isActive.proj table.coords;
          let table.height.proj := fun typedTuple ↦ typedTuple 2;
          let table.height := table.height.proj table.coords;
          decide (table.age > 30) && table.isActive && decide (table.height < 180))
        table).mapByList
    [("table.age", SQLTypeProxy.int), ("table.height", SQLTypeProxy.float)] fun table.coords ↦
    let table.age.proj := fun typedTuple ↦ typedTuple 0;
    let table.age := table.age.proj table.coords;
    let table.height.proj := fun typedTuple ↦ typedTuple 2;
    let table.height := table.height.proj table.coords;
    TypedTupleOfList.cons SQLTypeProxy.int table.age
      (TypedTupleOfList.cons SQLTypeProxy.float table.height
        TypedTupleOfList.nil) : TypedRelationOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float] →
  TypedRelation
    (colTypeOfList (List.map (fun x ↦ x.2) [("table.age", SQLTypeProxy.int), ("table.height", SQLTypeProxy.float)]))
-/
#guard_msgs in
#check egSqlQuery₂

-- example : egSqlQuery₃ := by
--   sorry

/--
info: fun table table2 ↦
  restriction
    (fun table.coords ↦
      let table.age.proj := fun typedTuple ↦ typedTuple 0;
      let table.age := table.age.proj table.coords;
      let table.isActive.proj := fun typedTuple ↦ typedTuple 1;
      let table.isActive := table.isActive.proj table.coords;
      let table.height.proj := fun typedTuple ↦ typedTuple 2;
      let table.height := table.height.proj table.coords;
      decide (table.age > 30) && table.isActive && decide (table.height < 180))
    (table.append
      table2) : TypedRelationOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float] →
  TypedRelationOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float] →
    TypedRelation
      (colTypeOfList
        [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float, SQLTypeProxy.int, SQLTypeProxy.bool,
          SQLTypeProxy.float])
-/
#guard_msgs in
#check egSqlQuery₃

/--
info: fun table ↦
  (restriction
        (fun table.coords ↦
          let table.age.proj := fun typedTuple ↦ typedTuple 0;
          let table.age := table.age.proj table.coords;
          let table.isActive.proj := fun typedTuple ↦ typedTuple 1;
          let table.isActive := table.isActive.proj table.coords;
          let table.height.proj := fun typedTuple ↦ typedTuple 2;
          let table.height := table.height.proj table.coords;
          decide (table.age > 30) && table.isActive && decide (table.height < 180))
        table).mapByList
    [("doubled_age", SQLTypeProxy.int)] fun table.coords ↦
    let table.age.proj := fun typedTuple ↦ typedTuple 0;
    let table.age := table.age.proj table.coords;
    TypedTupleOfList.cons SQLTypeProxy.int (2 * table.age)
      TypedTupleOfList.nil : TypedRelationOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float] →
  TypedRelation (colTypeOfList (List.map (fun x ↦ x.2) [("doubled_age", SQLTypeProxy.int)]))
-/
#guard_msgs in
#check egSqlQuery₄

/--
info: groupSumsExprs generated
---
info: groupCountExpr generated
---
info: fun table ↦
  (restriction
        (fun table.coords ↦
          let table.age.proj := fun typedTuple ↦ typedTuple 0;
          let table.age := table.age.proj table.coords;
          let table.isActive.proj := fun typedTuple ↦ typedTuple 1;
          let table.isActive := table.isActive.proj table.coords;
          let table.height.proj := fun typedTuple ↦ typedTuple 2;
          let table.height := table.height.proj table.coords;
          decide (table.age > 30) && table.isActive && decide (table.height < 180))
        table).mapByList
    [("count", SQLTypeProxy.int)] fun table.coords ↦
    let countAll.proj := fun table.coords ↦
      (fun k ↦
          Int.ofNat
            (groupCount (fun typedTuple ↦ TypedTupleOfList.cons SQLTypeProxy.int (typedTuple 0) TypedTupleOfList.nil) k
              table))
        ((fun typedTuple ↦ TypedTupleOfList.cons SQLTypeProxy.int (typedTuple 0) TypedTupleOfList.nil) table.coords);
    let countAll := countAll.proj table.coords;
    TypedTupleOfList.cons SQLTypeProxy.int countAll
      TypedTupleOfList.nil : TypedRelationOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float] →
  TypedRelation (colTypeOfList (List.map (fun x ↦ x.2) [("count", SQLTypeProxy.int)]))
-/
#guard_msgs in
#check egSqlQuery₅

set_option pp.funBinderTypes true in
example : egTypedTupleFilter% = egTypedTupleFilter%% := by
  grind

set_option pp.funBinderTypes true in
example : egTypedRelFilter% = egTypedRelFilter%% := by
  grind

end LeanDatabase
