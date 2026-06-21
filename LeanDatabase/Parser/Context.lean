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

def withLetColumnVars  (schema : List ((Name × SQLTypeProxy) × Expr)) (typedTupleVar : Expr) (usedName : Name → Bool)
    (k : Array Expr → TermElabM α )  : TermElabM α := do
  match schema with
  | [] => k #[]
  | ((name, colType), projExpr) :: rest => do
    let colTypeExpr := typeExpr colType
    let funcName := name ++ `proj
    let relType ← inferType typedTupleVar
    let funcType ← mkArrow relType colTypeExpr
    withLetDecl funcName funcType projExpr fun funcVar => do
      let colExpr ← mkAppM' funcVar #[typedTupleVar]
      let colExpr ← reduce colExpr
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

def expandNames (labels : List Name) (stx: Syntax) : MetaM Syntax := do
  let pairs ← labels.filterMapM fun label => do
    let shorter? := label.components.getLast?
    pure <| shorter?.map fun shorter => (shorter, label)
  stx.replaceM fun id => do
    let idName := id.getId
    match pairs.find? (fun (shorter, _) => shorter == idName) with
    | some (_, full) => pure <| mkIdent full
    | none => pure none

def withSchemasTupleVars (schemas : List (Name × List (Name × SQLTypeProxy))) (usedName : Name → Bool)
    (k : List (Expr × Array Expr) → TermElabM α) : TermElabM α := do
  match schemas with
  | [] => k []
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
      withLetColumnVars  schemaExprs typedTuple usedName
        fun letVars => do
      withSchemasTupleVars rest usedName fun rest =>
       k ((typedTuple, letVars) :: rest)

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

/-! ## Per-operator elaborators -/

-- This is the "WHERE" part of a SQL query, which is a function from a TypedRelation to a TypedRelation. This is to be applied to the database, which may be a single schema or built from multiple schemas.
def elabTypedTupleFilter (schemas : List (Name × List (Name × SQLTypeProxy))) (stx: Syntax) : TermElabM Expr := do
  withSchemasTupleVars schemas (stx.hasIdent) (fun vars =>
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
    let colExprs := colExprsTypes.map (fun (_, e) => e)
    let types := colExprsTypes.map (fun (t, _) => t)
    let e ← mkLambdaLetsFVars vars (exprTypedTuple colExprs)
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
