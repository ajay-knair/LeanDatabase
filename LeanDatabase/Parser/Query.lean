import LeanDatabase.Parser.Context
import LeanDatabase.Operators.CrossProduct
import LeanDatabase.Operators.Select
import LeanDatabase.Operators.OrderLimit

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
This is the main entry point for parsing a full SQL query (`SELECT` / `FROM` / `WHERE` / `GROUP BY`),
plus the binary set operators `UNION` / `UNION ALL` / `INTERSECT` / `EXCEPT` and parenthesised
grouping. Returns a function of the table variables, comparable for equality with `sql_equiv`.

Set-op arms recurse on each side (both return `fun tables => relation`), then β-apply the table vars
to recover each relation body, combine with `union` / `intersection`, etc. and re-bind once.
-/
partial def elabSqlQueryCore (tableVars : List (Expr × Name × List (Name × SQLTypeProxy))) (stx: Syntax) :
    TermElabM (Expr × List (Name × SQLTypeProxy)) :=  do
  let stx ← escapeJoin stx
  let vars := tableVars.map (fun (relVar, _, _) => relVar)
  match stx with
  | `(sql_query| ( $q:sql_query )) => elabSqlQueryCore tableVars q
  | `(sql_query| $l:sql_query $op:sql_setop $r:sql_query) => do
    let (lamL, schemaL) ← elabSqlQueryCore tableVars l
    let (lamR, schemaR) ← elabSqlQueryCore tableVars r
    unless schemaL.map (·.2) == schemaR.map (·.2) do
      throwError "set operation requires both queries to have the same column types"
    let opName ← match op with
      | `(sql_setop| UNION ALL) | `(sql_setop| UNION) => pure ``union
      | `(sql_setop| INTERSECT) => pure ``intersection
      | `(sql_setop| EXCEPT)    => pure ``minus
      | _ => throwError "unknown set operation"
    let combined ← mkAppM opName #[lamL.beta vars.toArray, lamR.beta vars.toArray]
    return (← mkLambdaFVars vars.toArray combined, schemaL)
  | `(sql_query| SELECT $[DISTINCT%$distinct?]? $sel:sql_cols FROM $dbs:sql_from $[WHERE $filter?]?
      $[ORDER BY $ord:sql_col,*]? $[LIMIT $lim:num]? $[;]?) => do
    let (productExpr, combinedSchema) ← productPair dbs
    let filteredExpr ← match filter? with
      | some filter => do
        let filter ← elabTypedTupleFilter [(`table, combinedSchema)] filter
        mkAppM ``restriction #[filter, productExpr]
      | none => pure productExpr
    let (rel, outSchema) ← match sel with
      | `(sql_cols| *) => pure (filteredExpr, combinedSchema)
      | `(sql_cols| $cols:sql_col,*) => do
        let colStxs := cols.getElems
        let cols := colStxs.map sqlColTerm
        let names := colStxs.map sqlColName |>.toList
        let nameStrs := names.map (·.toString)
        let (m, types) ← elabTypedTupleProjection [(`table, combinedSchema)] cols.toList
        let nameTypeExpr := toExpr <| nameStrs.zip types
        let e' ← mkAppM ``TypedRelation.mapByList #[filteredExpr, nameTypeExpr, m]
        pure (e', names.zip types)
      | _ => throwError "Unexpected syntax for SQL query"
    -- DISTINCT / ORDER BY / LIMIT are all the identity on a `Finset` (erased by `sql_equiv`).
    let rel ← if distinct?.isSome then mkAppM ``distinct #[rel] else pure rel
    let rel ← match ord with
      | none => pure rel
      | some ords => do
        let (key, _) ← elabTypedTupleProjection [(`table, outSchema)] (ords.getElems.toList.map sqlColTerm)
        mkAppM ``orderBy #[key, rel]
    let rel ← match lim with
      | none => pure rel
      | some k => mkAppM ``limit #[toExpr k.getNat, rel]
    return (← mkLambdaFVars vars.toArray rel, outSchema)
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

def egSqlQuery₆ := parseSqlQuery [(`table, [(`age, .int), (`isActive, .bool), (`height, .float)])] "SELECT SUM(age) AS count FROM table WHERE age > 30 && isActive && height < 180 GROUP BY isActive"

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

elab "egSqlQuery₆" : term => do
  let (e, _) ← egSqlQuery₆
  return e

set_option pp.funBinderTypes true in
/--
info: fun (table : TypedRelationOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float]) ↦
  restriction
    (fun (table.coords : TypedTupleOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float]) ↦
      let table.age := table.coords 0;
      let table.isActive := table.coords 1;
      let table.height := table.coords 2;
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
          let table.age := table.coords 0;
          let table.isActive := table.coords 1;
          let table.height := table.coords 2;
          decide (table.age > 30) && table.isActive && decide (table.height < 180))
        table).mapByList
    [("table.age", SQLTypeProxy.int)] fun table.coords ↦
    let table.age := table.coords 0;
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
          let table.age := table.coords 0;
          let table.isActive := table.coords 1;
          let table.height := table.coords 2;
          decide (table.age > 30) && table.isActive && decide (table.height < 180))
        table).mapByList
    [("table.age", SQLTypeProxy.int), ("table.height", SQLTypeProxy.float)] fun table.coords ↦
    let table.age := table.coords 0;
    let table.height := table.coords 2;
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
      let table.age := table.coords 0;
      let table.isActive := table.coords 1;
      let table.height := table.coords 2;
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
          let table.age := table.coords 0;
          let table.isActive := table.coords 1;
          let table.height := table.coords 2;
          decide (table.age > 30) && table.isActive && decide (table.height < 180))
        table).mapByList
    [("doubled_age", SQLTypeProxy.int)] fun table.coords ↦
    let table.age := table.coords 0;
    TypedTupleOfList.cons SQLTypeProxy.int (2 * table.age)
      TypedTupleOfList.nil : TypedRelationOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float] →
  TypedRelation (colTypeOfList (List.map (fun x ↦ x.2) [("doubled_age", SQLTypeProxy.int)]))
-/
#guard_msgs in
#check egSqlQuery₄

/--
info: fun table ↦
  (restriction
        (fun table.coords ↦
          let table.age := table.coords 0;
          let table.isActive := table.coords 1;
          let table.height := table.coords 2;
          decide (table.age > 30) && table.isActive && decide (table.height < 180))
        table).mapByList
    [("count", SQLTypeProxy.int)] fun table.coords ↦
    let countAll :=
      (fun k ↦
          Int.ofNat
            (groupCount (fun typedTuple ↦ TypedTupleOfList.cons SQLTypeProxy.int (typedTuple 0) TypedTupleOfList.nil) k
              table))
        ((fun typedTuple ↦ TypedTupleOfList.cons SQLTypeProxy.int (typedTuple 0) TypedTupleOfList.nil) table.coords);
    TypedTupleOfList.cons SQLTypeProxy.int countAll
      TypedTupleOfList.nil : TypedRelationOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float] →
  TypedRelation (colTypeOfList (List.map (fun x ↦ x.2) [("count", SQLTypeProxy.int)]))
-/
#guard_msgs in
#check egSqlQuery₅

/--
info: fun table ↦
  (restriction
        (fun table.coords ↦
          let table.age := table.coords 0;
          let table.isActive := table.coords 1;
          let table.height := table.coords 2;
          decide (table.age > 30) && table.isActive && decide (table.height < 180))
        table).mapByList
    [("count", SQLTypeProxy.int)] fun table.coords ↦
    let table.age.sum :=
      (fun k ↦
          groupSum (fun typedTuple ↦ TypedTupleOfList.cons SQLTypeProxy.bool (typedTuple 1) TypedTupleOfList.nil) k
            table fun typedTuple ↦ typedTuple 0)
        ((fun typedTuple ↦ TypedTupleOfList.cons SQLTypeProxy.bool (typedTuple 1) TypedTupleOfList.nil) table.coords);
    TypedTupleOfList.cons SQLTypeProxy.int table.age.sum
      TypedTupleOfList.nil : TypedRelationOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float] →
  TypedRelation (colTypeOfList (List.map (fun x ↦ x.2) [("count", SQLTypeProxy.int)]))
-/
#guard_msgs in
#check egSqlQuery₆

set_option pp.funBinderTypes true in
example : egTypedTupleFilter% = egTypedTupleFilter%% := by
  grind

set_option pp.funBinderTypes true in
example : egTypedRelFilter% = egTypedRelFilter%% := by
  grind

end LeanDatabase
