import Lean
import Mathlib
import LeanDatabase.TypedRelation

/-!
# SQL type reification (`SQLTypeProxy`) and list-indexed schemas

The foundational layer of the parser: a closed, finite universe of SQL column types
(`SQLTypeProxy`) that maps to concrete Lean types, plus the canonical *list-indexed* schema
encoding (`colTypeOfList` / `TypedTupleOfList` / `TypedRelationOfList`) that every parsed query
elaborates against.

This file deliberately depends only on `TypedRelation` (no SQL syntax), so the syntax layer and
the type layer can be developed independently — the elaboration layer (`Parser.Context`,
`Parser.Query`) is what ties them together.
-/

open Lean Meta

namespace LeanDatabase

/-- The closed universe of SQL column types we model. `ToExpr` lets the meta layer reflect a proxy
back into a term; `DecidableEq` drives the schema decidable-equality instance below. -/
inductive SQLTypeProxy where
  | int
  | bool
  | float
  | string
  | timestamp
deriving Repr, DecidableEq, ToExpr


/-- The Lean type a proxy denotes. `@[reducible]` so type-class search sees through it. -/
@[reducible]
def SQLTypeProxy.type : SQLTypeProxy → Type
  | .int => Int
  | .bool => Bool
  | .float => Rat
  | .string => String
  | .timestamp => String

def SQLTypeProxy.list : List SQLTypeProxy := [.int, .bool, .float, .string, .timestamp]

instance (t : SQLTypeProxy) : DecidableEq t.type :=
  match t with
  | .int => inferInstance
  | .bool => inferInstance
  | .float => inferInstance
  | .string => inferInstance
  | .timestamp => inferInstance

/-- The `Expr` of the Lean type a proxy denotes (the term-level mirror of `SQLTypeProxy.type`). -/
def typeExpr (t : SQLTypeProxy) : Expr :=
  match t with
  | .int => mkConst ``Int
  | .bool => mkConst ``Bool
  | .float => mkConst ``Rat
  | .string => mkConst ``String
  | .timestamp => mkConst ``String

/-- Map a DDL type string (`VARCHAR(…)`, `BIGINT`, `TIMESTAMP`, …) to a proxy. Matched by prefix,
defaulting to `string` for anything unrecognized. -/
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
  else if s.startsWith "varchar" then .string
  else if s.startsWith "date" then .string
  else if s.startsWith "timestamp" then .timestamp
  else .string -- default to string for unrecognized types

/-- A schema as `Fin n → Type`, indexing a `List SQLTypeProxy` positionally. This is the canonical
form every parsed query targets. -/
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

@[reducible]
def TypedTupleOfList.nil : TypedTupleOfList [] := fun ⟨i, hi⟩ => by simp at hi

@[reducible]
def TypedTupleOfList.cons (t : SQLTypeProxy) (x: t.type) (ts : TypedTupleOfList rest) :
  TypedTupleOfList (t :: rest) := fun ⟨i, hi⟩ =>
  match i with
  | 0 => by simp [colTypeOfList]; exact x
  | j+1 => ts ⟨j, by grind⟩

/-- A single-column `TypedTupleOfList` is determined by its one entry — lets `simp`/`grind` reduce
a `key t = k` equality between wrapped `GROUP BY` keys down to plain component equality, which is
what the `HAVING`/`WHERE` predicate is actually stated in terms of. -/
@[simp]
theorem TypedTupleOfList.cons_nil_inj {t : SQLTypeProxy} {x y : t.type} :
    (TypedTupleOfList.cons t x TypedTupleOfList.nil = TypedTupleOfList.cons t y TypedTupleOfList.nil) ↔ x = y := by
  constructor
  · intro h
    have := congrFun h (0 : Fin 1)
    simpa [TypedTupleOfList.cons, colTypeOfList] using this
  · rintro rfl
    rfl

@[reducible]
def TypedTupleOfList.append (ts1 : TypedTupleOfList l1) (ts2 : TypedTupleOfList l2) :
  TypedTupleOfList (l1 ++ l2) := match l1 with
  | [] => ts2
  | t :: rest => TypedTupleOfList.cons t (ts1 ⟨0, by simp⟩) (TypedTupleOfList.append (fun ⟨i, hi⟩ => ts1 ⟨i+1, by grind⟩)  ts2)

@[reducible]
def TypedRelationOfList.nil : TypedRelationOfList [] :=
  {labels := fun ⟨i, hi⟩ => by simp at hi, rows := Finset.empty}

@[reducible]
def TypedRelationOfList.append (r1 : TypedRelationOfList l1) (r2 : TypedRelationOfList l2) :
  TypedRelationOfList (l1 ++ l2) :=
  {labels := fun ⟨i, hi⟩ => by
    simp at hi
    exact if h : i < l1.length then r1.labels ⟨i, h⟩ else r2.labels ⟨i - l1.length, by grind⟩,
   rows := (r1.rows ×ˢ r2.rows).image (fun ((ts1 : TypedTupleOfList l1), (ts2 : TypedTupleOfList l2)) => TypedTupleOfList.append ts1 ts2)}


/-- Reflect a `List SQLTypeProxy` into the `Expr` of the corresponding Lean-level list. -/
def sqlTypeListExpr (l: List SQLTypeProxy) : MetaM Expr := do
  match l with
  | [] => mkAppOptM ``List.nil #[mkConst ``SQLTypeProxy]
  | t :: rest =>
    mkAppM ``List.cons #[toExpr t, ← sqlTypeListExpr rest]

end LeanDatabase
