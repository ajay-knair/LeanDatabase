import LeanDatabase.Parser.Context
import LeanDatabase.Operators.CrossProduct
import LeanDatabase.Operators.Select
import LeanDatabase.Operators.OrderLimit
import LeanDatabase.Operators.Join

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
      | some filter => elabWhere productExpr combinedSchema filter
      | none => pure productExpr
    let (rel, outSchema) ← match sel with
      | `(sql_cols| *) => pure (filteredExpr, combinedSchema)
      | `(sql_cols| $cols:sql_col,*) => do
        let colStxs := cols.getElems
        let cols := colStxs.map sqlColTerm
        let names := colStxs.map sqlColName |>.toList
        let nameStrs := names.map (·.toString)
        let (m, types) ← elabTypedTupleProjection [(.anonymous, combinedSchema)] cols.toList
        let nameTypeExpr := toExpr <| nameStrs.zip types
        let e' ← mkAppM ``TypedRelation.mapByList #[filteredExpr, nameTypeExpr, m]
        pure (e', names.zip types)
      | _ => throwError "Unexpected syntax for SQL query"
    -- DISTINCT / ORDER BY / LIMIT are all the identity on a `Finset` (erased by `sql_equiv`).
    let rel ← if distinct?.isSome then mkAppM ``distinct #[rel] else pure rel
    let rel ← match ord with
      | none => pure rel
      | some ords => do
        let (key, _) ← elabTypedTupleProjection [(.anonymous, outSchema)] (ords.getElems.toList.map sqlColTerm)
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
        let filter ← elabTypedTupleFilter [(.anonymous, combinedSchema)] filter
        mkAppM ``restriction #[filter, productExpr]
      | none => pure productExpr
    let colStxs := cols.getElems
    let cols := colStxs.map sqlColTerm
    let names := colStxs.map sqlColName |>.toList
    let nameStrs := names.map (·.toString)
    let (m, types) ← elabTypedTupleGroupProjection [(.anonymous, combinedSchema)] cols.toList inGroup filteredExpr
    let havingFilteredExpr ← match having? with
      | some having => do
        let h ← elabTypedTupleGroupFilter
          [(.anonymous, combinedSchema)] having inGroup filteredExpr
        mkAppM ``restriction #[h, filteredExpr]
      | none => pure filteredExpr
    let nameTypeExpr := toExpr <| nameStrs.zip types
    let e' ← mkAppM ``TypedRelation.mapByList #[havingFilteredExpr, nameTypeExpr, m]
    return (← mkLambdaFVars vars.toArray e', names.zip types)
  | _ => throwError "Unexpected syntax for SQL query"
  where
  -- The FROM relation + its schema
  productPair (dbs: TSyntax `sql_from) : TermElabM (Expr × List (Name × SQLTypeProxy)) := do
    match dbs with
    | `(sql_from| $db:ident) => do
      let .some (tableExpr, _, columns) :=
        tableVars.findSome? (fun (e, name, cols) => if name == db.getId then some (e, name, cols) else none)
        | throwError s!"Unknown table {db.getId}"
      return (tableExpr, columns)
    | `(sql_from| ( $sub:sql_query ) AS $_alias:ident) => do
      let (lamSub, subSchema) ← elabSqlQueryCore tableVars sub
      let vars := tableVars.map (fun (relVar, _, _) => relVar)
      return (lamSub.beta vars.toArray, subSchema)
    | `(sql_from| $f1:sql_from , $f2:sql_from) => do
      let (e1, s1) ← productPair f1
      let (e2, s2) ← productPair f2
      return (← mkAppM ``TypedRelationOfList.append #[e1, e2], s1 ++ s2)
    | _ => throwError "Unsupported FROM clause: {← PrettyPrinter.ppCategory `sql_from dbs}"
  -- Apply a `WHERE` clause to `rel`. `[NOT] EXISTS (subquery)` and `x [NOT] IN (subquery)` become a
  -- `semijoin`/`antijoin`; anything else is an ordinary `restriction` by a tuple predicate.
  elabWhere (rel : Expr) (schema : List (Name × SQLTypeProxy)) (filter : Term) : TermElabM Expr := do
    match filter with
    | `(EXISTS ( $inner:sql_query ))     => elabExists rel schema inner none false
    | `(NOT EXISTS ( $inner:sql_query )) => elabExists rel schema inner none true
    | `($oc:term IN ( $inner:sql_query ))     => elabExists rel schema inner (some oc) false
    | `($oc:term NOT IN ( $inner:sql_query )) => elabExists rel schema inner (some oc) true
    | _ => do
      let f ← elabTypedTupleFilter [(.anonymous, schema)] filter
      mkAppM ``restriction #[f, rel]

  elabExists (rel : Expr) (outerSchema : List (Name × SQLTypeProxy)) (inner : TSyntax `sql_query)
      (inCol? : Option Term) (isNeg : Bool) : TermElabM Expr := do
    match inner with
    | `(sql_query| SELECT $sel:sql_cols FROM $sdb:sql_from $[WHERE $corr?]? $[;]?) => do
      let some innerName := (getIdents sdb).head? | throwError "subquery expects a single inner table"
      let (sExpr, sSchema) ← productPair sdb
      let corr ← match inCol?, corr? with
        | some oc, _ => do                                  -- `oc IN (SELECT c FROM …)`  ⇒  `oc = c`
          match sel with
          | `(sql_cols| $c:sql_col,*) =>
            let #[col] := c.getElems | throwError "IN subquery must SELECT exactly one column"
            `($oc = $(sqlColTerm col))
          | _ => throwError "IN subquery must SELECT exactly one column"
        | none, some corr => pure corr                      -- `EXISTS (… WHERE corr)`
        | none, none => throwError "EXISTS subquery needs a correlating WHERE condition"
      let cond ← elabTypedTupleFilter [(.anonymous, outerSchema), (innerName, sSchema)] corr
      mkAppM (if isNeg then ``antijoin else ``semijoin) #[rel, sExpr, cond]
    | _ => throwError "subquery expects `SELECT … FROM table …`"

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

def egSqlQuery₇ := parseSqlQuery [(`table, [(`age, .int), (`isActive, .bool), (`height, .float)])] "SELECT SUM(age) AS sum FROM table WHERE age > 30 && isActive && height < 180 GROUP BY isActive HAVING SUM(age) < 100"

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

elab "egSqlQuery₇" : term => do
  let (e, _) ← egSqlQuery₇
  return e


#check egTypedTupleFilter%
set_option pp.funBinderTypes true in
/--
info: fun (table : TypedRelationOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float]) ↦
  restriction
    (fun (coords : TypedTupleOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float]) ↦
      let table.age := coords 0;
      let table.isActive := coords 1;
      let table.height := coords 2;
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
        (fun coords ↦
          let table.age := coords 0;
          let table.isActive := coords 1;
          let table.height := coords 2;
          decide (table.age > 30) && table.isActive && decide (table.height < 180))
        table).mapByList
    [("table.age", SQLTypeProxy.int)] fun coords ↦
    let table.age := coords 0;
    TypedTupleOfList.cons SQLTypeProxy.int table.age
      TypedTupleOfList.nil : TypedRelationOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float] →
  TypedRelation (colTypeOfList (List.map (fun x ↦ x.2) [("table.age", SQLTypeProxy.int)]))
-/
#guard_msgs in
#check egSqlQuery₁


/--
info: fun table ↦
  (restriction
        (fun coords ↦
          let table.age := coords 0;
          let table.isActive := coords 1;
          let table.height := coords 2;
          decide (table.age > 30) && table.isActive && decide (table.height < 180))
        table).mapByList
    [("table.age", SQLTypeProxy.int), ("table.height", SQLTypeProxy.float)] fun coords ↦
    let table.age := coords 0;
    let table.height := coords 2;
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
    (fun coords ↦
      let table.age := coords 0;
      let table.isActive := coords 1;
      let table.height := coords 2;
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
        (fun coords ↦
          let table.age := coords 0;
          let table.isActive := coords 1;
          let table.height := coords 2;
          decide (table.age > 30) && table.isActive && decide (table.height < 180))
        table).mapByList
    [("doubled_age", SQLTypeProxy.int)] fun coords ↦
    let table.age := coords 0;
    TypedTupleOfList.cons SQLTypeProxy.int (2 * table.age)
      TypedTupleOfList.nil : TypedRelationOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float] →
  TypedRelation (colTypeOfList (List.map (fun x ↦ x.2) [("doubled_age", SQLTypeProxy.int)]))
-/
#guard_msgs in
#check egSqlQuery₄

/--
info: fun table ↦
  (restriction
        (fun coords ↦
          let table.age := coords 0;
          let table.isActive := coords 1;
          let table.height := coords 2;
          decide (table.age > 30) && table.isActive && decide (table.height < 180))
        table).mapByList
    [("count", SQLTypeProxy.int)] fun coords ↦
    let countAll :=
      (fun k ↦
          Int.ofNat
            (groupCount (fun typedTuple ↦ TypedTupleOfList.cons SQLTypeProxy.int (typedTuple 0) TypedTupleOfList.nil) k
              (restriction (fun coords ↦ decide (coords 0 > 30) && coords 1 && decide (coords 2 < 180)) table)))
        ((fun typedTuple ↦ TypedTupleOfList.cons SQLTypeProxy.int (typedTuple 0) TypedTupleOfList.nil) coords);
    TypedTupleOfList.cons SQLTypeProxy.int countAll
      TypedTupleOfList.nil : TypedRelationOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float] →
  TypedRelation (colTypeOfList (List.map (fun x ↦ x.2) [("count", SQLTypeProxy.int)]))
-/
#guard_msgs in
#check egSqlQuery₅


/--
info: fun table ↦
  (restriction
        (fun coords ↦
          let table.age := coords 0;
          let table.isActive := coords 1;
          let table.height := coords 2;
          decide (table.age > 30) && table.isActive && decide (table.height < 180))
        table).mapByList
    [("count", SQLTypeProxy.int)] fun coords ↦
    let table.age.sum :=
      (fun k ↦
          groupSum (fun typedTuple ↦ TypedTupleOfList.cons SQLTypeProxy.bool (typedTuple 1) TypedTupleOfList.nil) k
            (restriction (fun coords ↦ decide (coords 0 > 30) && coords 1 && decide (coords 2 < 180)) table)
            fun typedTuple ↦ typedTuple 0)
        ((fun typedTuple ↦ TypedTupleOfList.cons SQLTypeProxy.bool (typedTuple 1) TypedTupleOfList.nil) coords);
    TypedTupleOfList.cons SQLTypeProxy.int table.age.sum
      TypedTupleOfList.nil : TypedRelationOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float] →
  TypedRelation (colTypeOfList (List.map (fun x ↦ x.2) [("count", SQLTypeProxy.int)]))
-/
#guard_msgs in
#check egSqlQuery₆

/--
info: fun table ↦
  (restriction
        (fun coords ↦
          let table.age.sum :=
            (fun k ↦
                groupSum (fun typedTuple ↦ TypedTupleOfList.cons SQLTypeProxy.bool (typedTuple 1) TypedTupleOfList.nil)
                  k (restriction (fun coords ↦ decide (coords 0 > 30) && coords 1 && decide (coords 2 < 180)) table)
                  fun typedTuple ↦ typedTuple 0)
              ((fun typedTuple ↦ TypedTupleOfList.cons SQLTypeProxy.bool (typedTuple 1) TypedTupleOfList.nil) coords);
          decide (table.age.sum < 100))
        (restriction
          (fun coords ↦
            let table.age := coords 0;
            let table.isActive := coords 1;
            let table.height := coords 2;
            decide (table.age > 30) && table.isActive && decide (table.height < 180))
          table)).mapByList
    [("sum", SQLTypeProxy.int)] fun coords ↦
    let table.age.sum :=
      (fun k ↦
          groupSum (fun typedTuple ↦ TypedTupleOfList.cons SQLTypeProxy.bool (typedTuple 1) TypedTupleOfList.nil) k
            (restriction (fun coords ↦ decide (coords 0 > 30) && coords 1 && decide (coords 2 < 180)) table)
            fun typedTuple ↦ typedTuple 0)
        ((fun typedTuple ↦ TypedTupleOfList.cons SQLTypeProxy.bool (typedTuple 1) TypedTupleOfList.nil) coords);
    TypedTupleOfList.cons SQLTypeProxy.int table.age.sum
      TypedTupleOfList.nil : TypedRelationOfList [SQLTypeProxy.int, SQLTypeProxy.bool, SQLTypeProxy.float] →
  TypedRelation (colTypeOfList (List.map (fun x ↦ x.2) [("sum", SQLTypeProxy.int)]))
-/
#guard_msgs in
#check egSqlQuery₇


set_option pp.funBinderTypes true in
example : egTypedTupleFilter% = egTypedTupleFilter%% := by
  grind

set_option pp.funBinderTypes true in
example : egTypedRelFilter% = egTypedRelFilter%% := by
  grind

end LeanDatabase
