import LeanDatabase.Parser.Types
import LeanDatabase.Parser.Syntax
import LeanDatabase.SQLToolbox

/-!
# Elaboration context + per-operator (algebra) elaborators

This is the layer that joins the *syntax* (`Parser.Syntax`) to the *type model* (`Parser.Types`):
-/

open Lean Meta Elab Term

namespace LeanDatabase

/-! ## Type-probing for `AS` expressions -/

/-- Elaborate a `SELECT`-list expression, discovering its column type by trying each proxy type in
turn and keeping the first that elaborates. -/
def elabAsSql (stx: Syntax) : TermElabM (SQLTypeProxy × Expr) := do
  let res? : Option (SQLTypeProxy × Expr) ← SQLTypeProxy.list.findSomeM? (fun t => do
    let typeExpr := typeExpr t
    try
      let e ← withoutErrToSorry do
        elabTermEnsuringType stx typeExpr
      Term.synthesizeSyntheticMVarsNoPostponing
      pure (t, e)
    catch _ => pure none
  )
  match res? with
  | some res => pure res
  | none => throwError s!"Failed to parse type in AS clause: {← PrettyPrinter.ppCategory `term stx}"

/-! ## Column-binding context -/

def withLetColumnVars  (columns : List ((Name × SQLTypeProxy) × Expr)) (typedTupleVar : Expr) (usedName : Name → Bool)
    (k : Array Expr → TermElabM α )  : TermElabM α := do
  match columns with
  | [] => k #[]
  | ((name, colType), projExpr) :: rest => do
    let colTypeExpr := typeExpr colType
    let funcName := name ++ `proj
    let tupleType ← inferType typedTupleVar
    let funcType ← mkArrow tupleType colTypeExpr
    withLetDecl funcName funcType projExpr fun funcVar => do
      let colExpr ← mkAppM' funcVar #[typedTupleVar]
      let colExpr ← zetaReduce colExpr
      withLetDecl name colTypeExpr colExpr fun localVar => do
        let letVars := #[funcVar, localVar]
        withLetColumnVars rest typedTupleVar usedName (fun restExpr => k (letVars ++ restExpr))

def mkLambdaLetsFVars (vars : List (Expr × Array Expr)) (k: TermElabM Expr) : TermElabM Expr := do
  match vars with
  | [] => k
  | (var, letVars) :: rest => do
    mkLambdaFVars #[var] (← mkLetFVars letVars (← mkLambdaLetsFVars rest k))

-- #eval Name.components `tableA.x |>.getLast?

def schemaWithFullNames (schemaName: Name) (schema : List (Name × SQLTypeProxy)) : List (Name × SQLTypeProxy) :=
  schema.map (fun (name, colType) =>
    let fullName :=
      if schemaName.isPrefixOf name then name else schemaName ++ name
    (fullName, colType))

theorem schemaWithFullNames_eq (schemaName: Name) (schema : List (Name × SQLTypeProxy)) :
    schemaWithFullNames schemaName schema = schema.map (fun (name, colType) =>
      let fullName := if schemaName.isPrefixOf name then name else schemaName ++ name
      (fullName, colType)) := by rfl

theorem schemaWithFullNames_length (schemaName: Name) (schema : List (Name × SQLTypeProxy)) :
    (schemaWithFullNames schemaName schema).length = schema.length := by simp [schemaWithFullNames]

syntax "COUNT" "(" "*" ")" : term
syntax "COUNT" "(" term ")" : term
syntax "SUM" "(" term ")" : term
syntax "AVG" "(" term ")" : term
syntax "MIN" "(" term ")" : term
syntax "MAX" "(" term ")" : term

def expandNames (labels : List Name) (stx: Syntax) : MetaM Syntax := do
  let pairs ← labels.filterMapM fun label => do
    let shorter? := label.components.getLast?
    pure <| shorter?.map fun shorter => (shorter, label.getPrefix)
  stx.replaceM fun id => do
    let idName := id.getId
    match pairs.find? (fun (shorter, _) => shorter.isPrefixOf idName) with
    | some (_, pfx) => pure <| mkIdent <| pfx ++ idName
    | none => return none

/--
Expressions for projection functions for each column in a schema, along with the type of the tuple that contains them.
-/
def columnProjectionsE (schema : List (Name × SQLTypeProxy)) :
  MetaM <| Expr × Expr × (List ((Name × SQLTypeProxy) × Expr)) := do
    let colTypes := schema.map (fun (_, colType) => colType)
    let listExpr ← sqlTypeListExpr colTypes
    let tupleType ← mkAppM ``TypedTupleOfList #[listExpr]
    let relType ← mkAppM ``TypedRelationOfList #[listExpr]
    let colExprs ← List.finRange colTypes.length |>.mapM fun i => do
        let index := toExpr i
        withLocalDeclD `typedTuple tupleType fun typedTuple => do
          let value ← mkAppM' typedTuple #[index]
          mkLambdaFVars #[typedTuple] value
    let schemaExprs := schema.zip colExprs
    return (tupleType, relType, schemaExprs)

def exprTypeListTuple (colExprsTypes : List (SQLTypeProxy × Expr)) : MetaM Expr := do
  colExprsTypes.foldrM (fun (colType, expr) acc => do
    mkAppM ``TypedTupleOfList.cons #[toExpr colType, expr, acc]) (mkConst ``TypedTupleOfList.nil)

/--
Projects onto a subcollection of columns. Returns expressions for the projection function, domain and codomain types.
-/
def subcolumsProjectionsE (schema : List (Name × SQLTypeProxy)) (includeColumn : Name → Bool) :
  MetaM <| Expr × Expr × Expr := do
    let colTypes := schema.map (fun (_, colType) => colType)
    let listExpr ← sqlTypeListExpr colTypes
    let domainE ← mkAppM ``TypedTupleOfList #[listExpr]
    let subcolTypes := schema.filterMap fun (name, colType) =>
      if includeColumn name then some colType else none
    let codomainE ← mkAppM ``TypedTupleOfList #[← sqlTypeListExpr subcolTypes]
    let projE ←
      withLocalDeclD `typedTuple domainE fun typedTuple => do
      let colExprs ← List.finRange schema.length |>.filterMapM fun i => do
        let index := toExpr i
        let (name, colType) := schema.get i
        if includeColumn name then do
          let value ← mkAppM' typedTuple #[index]
          pure <| some (colType, value)
        else
          pure none
      let value ← exprTypeListTuple colExprs
      mkLambdaFVars #[typedTuple] value
    return (projE, domainE, codomainE)

/--
info: LeanDatabase.TypedAgg.groupSum {n : ℕ} {colType : Fin n → Type} [(i : Fin n) → DecidableEq (colType i)] {K : Type}
  [DecidableEq K] (key : TypedTuple colType → K) (k : K) (rel : TypedRelation colType) (f : TypedTuple colType → ℤ) : ℤ
-/
#guard_msgs in
#check groupSum

/--
info: LeanDatabase.TypedAgg.groupCount {n : ℕ} {colType : Fin n → Type} [(i : Fin n) → DecidableEq (colType i)] {K : Type}
  [DecidableEq K] (key : TypedTuple colType → K) (k : K) (rel : TypedRelation colType) : ℕ
-/
#guard_msgs in
#check groupCount


-- Looks like exactly the same code as `withLetColumnVars`, but with projections replaced by aggregate functions. Could be refactored to share code.
def withLetAggregateColumnVars  (columns : List ((Name × SQLTypeProxy) × Expr)) (typedTupleVar : Expr) (usedName : Name → Bool)
    (k : Array Expr → TermElabM α )  : TermElabM α := do
  match columns with
  | [] => k #[]
  | ((name, colType), projExpr) :: rest => do
    let colTypeExpr := typeExpr colType
    let funcName := name ++ `proj
    let tupleType ← inferType typedTupleVar
    let funcType ← mkArrow tupleType colTypeExpr
    withLetDecl funcName funcType projExpr fun funcVar => do
      let colExpr ← mkAppM' funcVar #[typedTupleVar]
      let colExpr ← reduce colExpr
      withLetDecl name colTypeExpr colExpr fun localVar => do
        let letVars := #[funcVar, localVar]
        withLetAggregateColumnVars rest typedTupleVar usedName (fun restExpr => k (letVars ++ restExpr))

def withSchemasTupleVars (schemas : List (Name × List (Name × SQLTypeProxy))) (usedName : Name → Bool)
    (k : List (Expr × Array Expr) → TermElabM α) : TermElabM α := do
  match schemas with
  | [] => k []
  | (schemaName, schema) :: rest => do
    let (type, _, columnExprs) ← columnProjectionsE (schemaWithFullNames schemaName schema)
    withLocalDeclD (schemaName ++ `coords) type fun typedTuple => do
      withLetColumnVars  columnExprs typedTuple usedName
        fun letVars => do
          withSchemasTupleVars rest usedName fun rest =>
          k ((typedTuple, letVars) :: rest)

/-- The aggregate operators we lift out of `SELECT`/`HAVING` over an arbitrary expression.
`SUM`/`MIN`/`MAX`/`AVG` share the shape `group<X> key k rel (f : TypedTuple → Int) : Int`;
`COUNT` is the row count (`groupCount`, no summand). Adding an aggregate = one constructor here
plus one `AggKind.op` line plus one match arm in `liftAggExprs`. -/
inductive AggKind where
  | sum | min | max | avg | count
  deriving DecidableEq

/-- The `group*` operator constant backing each summand aggregate. -/
def AggKind.op : AggKind → Name
  | .sum => ``groupSum
  | .min => ``groupMinInt
  | .max => ``groupMaxInt
  | .avg => ``groupAvg
  | .count => ``groupCount

/-- Builds one grouped aggregate per lifted `(freshName, kind, expr)`: each `expr` is elaborated
against a fresh tuple of `schema` into a `TypedTuple → Int` summand and fed to the operator named by
`kind.op`. `COUNT` ignores the summand and counts rows. -/
def groupAggExprsE (schema : List (Name × SQLTypeProxy)) (columnInGroup : Name → Bool)
    (typedTupleVar relE : Expr) (aggs : List (Name × AggKind × Syntax.Term)) :
    TermElabM (List ((Name × SQLTypeProxy) × Expr)) := do
  if aggs.isEmpty then return []
  let (keyMapE, _, codomainE) ← subcolumsProjectionsE schema columnInGroup
  let keyValue ← mkAppM' keyMapE #[typedTupleVar]
  aggs.mapM fun (name, kind, exprStx) => do
    -- summand `fun (t : TypedTuple schema) => (exprStx : Int)` (unused for COUNT)
    let projE? ← match kind with
      | .count => pure none
      | _ => do
          let projE ← withSchemasTupleVars [(.anonymous, schema)] (fun _ => true) fun vars =>
            mkLambdaLetsFVars vars (elabTermEnsuringType exprStx (mkConst ``Int))
          pure (some projE)
    let aggE ← withLocalDeclD `k codomainE fun keyVar => do
      let call ← match projE? with
        | none => do mkAppM ``Int.ofNat #[← mkAppM ``groupCount #[keyMapE, keyVar, relE]]
        | some projE => mkAppM kind.op #[keyMapE, keyVar, relE, projE]
      mkLambdaFVars #[keyVar] call
    let aggValue ← mkAppM' aggE #[keyValue]
    let aggValue ← mkLambdaFVars #[typedTupleVar] aggValue
    pure ((name, SQLTypeProxy.int), aggValue)

def withSchemasGroupedTupleVars (schemas : List (Name × List (Name × SQLTypeProxy))) (usedName : Name → Bool)
    (inGroup : Name → Bool) (relE : Expr) (aggs : List (Name × AggKind × Syntax.Term))
    (k : List (Expr × Array Expr) → TermElabM α) : TermElabM α := do
  match schemas with
  | [] => k []
  | (schemaName, schema) :: rest => do
    let schema := schemaWithFullNames schemaName schema
    let (type, _, columnExprs) ← columnProjectionsE schema
    let columnExprs := columnExprs.filter fun ((name, _), _) =>
        inGroup name
    withLocalDeclD (schemaName ++ `coords) type fun typedTupleE => do
      -- Group-key columns stay bound as plain columns; every aggregate (over a column or an
      -- arbitrary expression) is lifted by `liftAggExprs` and built here via `groupAggExprsE`.
      let groupAggExprsExprs ← groupAggExprsE schema inGroup typedTupleE relE aggs
      let columnExprs := columnExprs ++ groupAggExprsExprs
      withLetColumnVars  columnExprs typedTupleE usedName
        fun letVars => do
          withSchemasGroupedTupleVars rest usedName inGroup relE [] fun rest =>
          k ((typedTupleE, letVars) :: rest)

def withTableVars (schemas : List (Name × List (Name × SQLTypeProxy)))  (k : List (Expr × Name × List (Name × SQLTypeProxy)) →  TermElabM α)  : TermElabM α := do
  match schemas with
  | [] => k []
  | (tableName, columns) :: rest => do
    let colTypes := columns.map (fun (_, colType) => colType)
    let listExpr ← sqlTypeListExpr colTypes
    let type ← mkAppM ``TypedRelationOfList #[listExpr]
    withLocalDeclD tableName type fun typedRel => do
      withTableVars rest ((fun l ↦ k ((typedRel, tableName, columns) :: l)))

/-! ## Building output tuples -/

def TypedTuple.cons {n : Nat} {colType : Fin n → Type} (a: α) (tuple : TypedTuple colType) :
    TypedTuple (Fin.cons α colType) := Fin.cons a tuple

def colTypeNil : Fin 0 → Type := fun ⟨i, h⟩ => by simp at h

def TypedTuple.nil : TypedTuple colTypeNil := fun ⟨i, h⟩ => by simp at h

def exprTypedTuple : List Expr → MetaM Expr
  | [] => return mkConst ``TypedTuple.nil
  | e :: es => do
    let rest ← exprTypedTuple es
    mkAppM ``TypedTuple.cons #[e, rest]

/-! ## Product / projection helpers (currently unused; kept for multi-table work) -/

section helpers

variable {n m : Nat}
variable {colType1 : Fin n → Type} [∀ i, DecidableEq (colType1 i)]
variable {colType2 : Fin m → Type} [∀ i, DecidableEq (colType2 i)]

def TypedRelation.map (f : TypedTuple colType1 → TypedTuple colType2) (labels : Fin m → String)
    (r : TypedRelation colType1) :
  TypedRelation colType2 := {labels := labels, rows := r.rows.image f}

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

end helpers

def TypedRelation.mapByList {colType : Fin n → Type} [∀ i, DecidableEq (colType i)] (r: TypedRelation colType) (l: List (String × SQLTypeProxy)) (f: TypedTuple colType → TypedTuple (colTypeOfList (l.map (·.2)))) :
    TypedRelation (colTypeOfList (l.map (·.2))) :=
      let h : (l.map (·.2)).length = (l.map (·.1)).length := by grind
      TypedRelation.map f (h ▸ (l.map (·.1)|>.get)) r

/-! ## Per-operator elaborators -/

-- This is the "WHERE" part of a SQL query, which is a function from a TypedRelation to a TypedRelation. This is to be applied to the database, which may be a single schema or built from multiple schemas.
def elabTypedTupleFilter (schemas : List (Name × List (Name × SQLTypeProxy))) (stx: Syntax) : TermElabM Expr := do
  withSchemasTupleVars schemas (stx.hasIdent) (fun vars =>
    mkLambdaLetsFVars vars (elabTermEnsuringType stx (mkConst ``Bool)))

def elabTypedTupleGroupFilter (schemas : List (Name × List (Name × SQLTypeProxy))) (stx: Syntax) (inGroup : Name → Bool) (relE: Expr) (aggs : List (Name × AggKind × Syntax.Term)) : TermElabM Expr := do
  withSchemasGroupedTupleVars schemas (stx.hasIdent) inGroup relE aggs (fun vars =>
    mkLambdaLetsFVars vars (elabTermEnsuringType stx (mkConst ``Bool)))

def elabTypedRelFilter (schemas : List (Name × List (Name × SQLTypeProxy))) (stx: Syntax) (combineRels : List Name → List Expr → TermElabM Expr) : TermElabM Expr := do
  withTableVars schemas fun tableVars => do
    let tableNames := tableVars.map (fun (_, name, _) => name)
    let vars := tableVars.map (fun (relVar, _, _) => relVar)
    let relVar ← combineRels tableNames vars
    let filter ← elabTypedTupleFilter schemas stx
    let e ← mkAppM ``restriction #[filter, relVar]
    mkLambdaFVars vars.toArray e


def elabTypedRelFilterSimple (schemas : List (Name × List (Name × SQLTypeProxy))) (stx: Syntax) :
  TermElabM Expr :=
  elabTypedRelFilter schemas stx fun _ vars =>
    match vars with
    | [relVar] => pure relVar
    | _ => throwError "Multiple tables in FROM clause not supported in this context"

def elabTypedTupleProjection (schemas : List (Name × List (Name × SQLTypeProxy))) (cols: List Syntax.Term) :
  TermElabM (Expr × List SQLTypeProxy) := do
  withSchemasTupleVars schemas (fun name => cols.any (fun col => col.raw.hasIdent name)) (fun vars => do
    let colExprsTypes ← cols.mapM elabAsSql
    -- let colExprs := colExprsTypes.map (fun (_, e) => e)
    let types := colExprsTypes.map (fun (t, _) => t)
    let e ← mkLambdaLetsFVars vars (exprTypeListTuple colExprsTypes)
    return (e, types)
  )

def elabTypedTupleGroupProjection (schemas : List (Name × List (Name × SQLTypeProxy))) (cols: List Syntax.Term) (inGroup : Name → Bool) (relE : Expr) (aggs : List (Name × AggKind × Syntax.Term)) :
  TermElabM (Expr × List SQLTypeProxy) := do
  withSchemasGroupedTupleVars schemas (fun name => cols.any (fun col => col.raw.hasIdent name)) inGroup relE aggs (fun vars => do
    let colExprsTypes ← cols.mapM elabAsSql
    -- let colExprs := colExprsTypes.map (fun (_, e) => e)
    let types := colExprsTypes.map (fun (t, _) => t)
    let e ← mkLambdaLetsFVars vars (exprTypeListTuple colExprsTypes)
    return (e, types)
  )

def elabTypedRelFilterProj (schemas : List (Name × List (Name × SQLTypeProxy)))
    (stx: Syntax) (colStxs : List (TSyntax `sql_col))
    (combineRels : List Name → List Expr → TermElabM Expr) : TermElabM (Expr × List SQLTypeProxy) := do
  withTableVars schemas fun tableVars => do
    let tableNames := tableVars.map (fun (_, name, _) => name)
    let rel ← combineRels tableNames (tableVars.map (fun (relVar, _, _) => relVar))
    let filter ← elabTypedTupleFilter schemas stx
    let e ← mkAppM ``restriction #[filter, rel]
    let cols := colStxs.map sqlColTerm
    let names := colStxs.map sqlColName
    let names := names.map (·.toString)
    let nameExpr := toExpr names
    let (m, types) ← elabTypedTupleProjection schemas cols
    let e' ← mkAppM ``TypedRelation.map #[m, nameExpr, e]
    let vars := tableVars.map (fun (relVar, _, _) => relVar)
    return (← mkLambdaFVars vars.toArray e', types)

end LeanDatabase
