import Mathlib

namespace LeanDatabase

variable {n : Nat}

/-!
## Typed Relations (Finset Definition)

We use `Finset` (Finite Sets) which allows us to compute cardinality
and guarantees finiteness, unlike `Set`. Our Databases are also finite
so this will help us in future.
-/

-- Finsets require Decidable Equality to handle deduplication
variable {types : Fin n → Type} [∀ i, DecidableEq (types i)]

abbrev TypedTuple (types : Fin n → Type) := (i : Fin n) → types i

-- We ensure tuples can be compared for equality
instance : DecidableEq (TypedTuple types) :=
  inferInstanceAs (DecidableEq ((i : Fin n) → types i))

/-! ## Definitions -/

@[ext, grind] structure TypedRelation (types : Fin n → Type) where
  labels : Fin n → String
  rows   : Finset (TypedTuple types)
deriving Inhabited

@[ext, grind] structure TypedListRelation (types : Fin n → Type) where
  labels : Fin n → String
  rows   : List (TypedTuple types)
deriving Inhabited

-- Definition of an Empty Relation (The "Zero" element)
def emptyRel (l : Fin n → String) : TypedRelation types :=
  { labels := l, rows := ∅ }

-- Convert List-Relation to Finset-Relation
@[simp, grind .]
def toFinsetRelation (r : TypedListRelation types) : TypedRelation types :=
  {
    labels := r.labels,
    rows   := r.rows.toFinset
  }

theorem permutation_implies_finset_equality
    (l1 l2 : TypedListRelation types) :
    l1.labels = l2.labels →
    List.Perm l1.rows l2.rows →
    toFinsetRelation l1 = toFinsetRelation l2 := by
  intro h_labels h_perm
  simp_all [toFinsetRelation]
  exact List.toFinset_eq_of_perm l1.rows l2.rows h_perm

/-! ## Relational Algebra Operations on Finsets -/

-- Projection (uses Finset.image)
@[simp]
def projection {m : Nat} (indices : Fin m → Fin n) (rel : TypedRelation types) :
    TypedRelation (fun j => types (indices j)) :=

  let _ : ∀ j, DecidableEq (types (indices j)) := fun _ => inferInstance
  {
    labels := fun j => rel.labels (indices j),
    rows   := rel.rows.image (fun t j => t (indices j))
  }

@[simp]
def typedColumn {α : Type} [DecidableEq α]
    (index : Fin n) (rel : TypedRelation types) (h : types index = α := by simp) : Finset α :=
  -- Cast the tuple value to alpha and image it
  rel.rows.image (fun tuple => h ▸ tuple index)

-- Restriction (uses Finset.filter)
@[simp, grind]
def restriction (predicate : TypedTuple types → Bool) (rel : TypedRelation types) :
    TypedRelation types :=
  {
    labels := rel.labels,
    rows   := rel.rows.filter (fun t => predicate t)
  }

-- Selection is same as restriction, but is also commonly used
def selection (predicate : TypedTuple types → Bool) (rel : TypedRelation types) :
    TypedRelation types :=
  restriction predicate rel

-- Union
@[simp, grind]
def union (r1 r2 : TypedRelation types) : TypedRelation types :=
  {
    labels := r1.labels,
    rows   := r1.rows ∪ r2.rows -- Finset Union
  }

-- Intersection
@[simp, grind]
def intersection (r1 r2 : TypedRelation types) : TypedRelation types :=
  {
    labels := r1.labels,
    rows   := r1.rows ∩ r2.rows -- Finset Intersection
  }

-- Minus / Difference
@[simp, grind]
def minus (r1 r2 : TypedRelation types) : TypedRelation types :=
  {
    labels := r1.labels,
    rows   := r1.rows \ r2.rows -- Finset Difference (sdiff)
  }

-- RENAME operator: Changes labels, keeps data exactly the same.
@[simp, grind]
def rename (newLabels : Fin n → String) (rel : TypedRelation types) : TypedRelation types :=
  {
    labels := newLabels,
    rows   := rel.rows
  }

-- Helper: Rename a specific column by index
def renameColumn (idx : Fin n) (newName : String) (rel : TypedRelation types) : TypedRelation types :=
  {
    labels := Function.update rel.labels idx newName,
    rows   := rel.rows
  }

-- Helper to prefix all labels in a relation, useful for cross product
@[simp]
def prefixLabels (prefixStr : String) (rel : TypedRelation types) : TypedRelation types :=
  {
    labels := fun i => prefixStr ++ "." ++ rel.labels i,
    rows   := rel.rows
  }


/-! ## Theorems -/

theorem projection_compose {m p : Nat}
    (indices1 : Fin m → Fin n) (indices2 : Fin p → Fin m)
    (rel : TypedRelation types) :
    projection indices2 (projection indices1 rel) =
    projection (fun j => indices1 (indices2 j)) rel := by
  simp only [projection]
  apply TypedRelation.ext
  · simp
  · simp only [Finset.image_image]
    grind

-- Projection removes duplicates, so size is <= original, not equal.
theorem projection_card_le {m : Nat} (indices : Fin m → Fin n)
    (rel : TypedRelation types) :
    (projection indices rel).rows.card ≤ rel.rows.card := by
  simp [projection]
  -- Law: |image f S| ≤ |S|
  apply Finset.card_image_le

omit [∀ i, DecidableEq (types i)] in
-- Theorem: Restriction Cardinality
-- |σ(R)| ≤ |R|
-- "Filtering rows can never increase the number of rows."
theorem restriction_card_le
    (predicate : TypedTuple types → Bool) (rel : TypedRelation types) :
    (restriction predicate rel).rows.card ≤ rel.rows.card := by
  simp [restriction]
  -- |filter p S| ≤ |S|
  apply Finset.card_filter_le


/-
### Formatting to print
-/

-- format a single tuple to: "[Val1, Val2, ...]"
def formatTuple [∀ i, ToString (types i)] (t : TypedTuple types) : String :=
  let parts := List.finRange n |>.map (fun i => toString (t i))
  "[" ++ (String.intercalate ", " parts) ++ "]"

-- Helper to format the whole table
-- Note: We use 'unsafe' to convert the Set of rows into a List for printing
unsafe def simpleFormat [∀ i, DecidableEq (types i)] [∀ i, ToString (types i)]
    (rel : TypedRelation types) : String :=
  let labelStr := "Labels: " ++ toString (List.ofFn rel.labels)

  -- unsafeCast allows us to view the Set as a List just for printing
  let rowList : List (TypedTuple types) := unsafeCast rel.rows.val
  let rowStrs := rowList.map (fun r => "Row:    " ++ formatTuple r)

  String.intercalate "\n" (labelStr :: rowStrs)

unsafe instance [∀ i, DecidableEq (types i)] [∀ i, ToString (types i)] :
    Repr (TypedRelation types) where
  reprPrec rel _ := simpleFormat rel
