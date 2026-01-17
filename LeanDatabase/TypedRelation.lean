import Mathlib

namespace LeanDatabase

/-!
## Typed Relations (Set-Theoretic Definition)
-/

abbrev TypedTuple {n : Nat} (types : Fin n → Type)[∀ a, DecidableEq (types a)] := (i : Fin n) → types i

#synth DecidableEq (Fin 3 →  Nat)
/-
Labels - Mapping from index to String labels
Rows - Data (in set) for all the TypedTuples
-/
@[ext]
structure TypedRelation {n : Nat} (types : Fin n → Type)[∀ a, DecidableEq (types a)] where
  labels : Fin n → String
  rows   : Set (TypedTuple types) -- Relations use Sets by definition
deriving Inhabited

@[ext]
structure TypedListRelation {n : Nat} (types : Fin n → Type)[∀ a, DecidableEq (types a)] where
  labels : Fin n → String
  rows   : List (TypedTuple types)
deriving Inhabited

-- Convert List-Relation to Set-Relation
@[simp, grind .]
def toSetRelation {n : Nat} {types : Fin n → Type}[∀ a, DecidableEq (types a)] (r : TypedListRelation types) : TypedRelation types :=
  {
    labels := r.labels,
    rows   := { t | t ∈ r.rows }
  }

theorem permutation_implies_set_equality {n : Nat} {types : Fin n → Type}[∀ a, DecidableEq (types a)]
    (l1 l2 : TypedListRelation types) :
    l1.labels = l2.labels →       -- Same Schema
    List.Perm l1.rows l2.rows →   -- Permutation of rows
    toSetRelation l1 = toSetRelation l2 := by
  intro h_labels h_perm
  simp [toSetRelation]
  grind


/-! ## Relational Algebra Operations on Sets -/

-- Projection of a Relation
@[simp]
def projection {n m : Nat} {types : Fin n → Type}[∀ a, DecidableEq (types a)]
    (indices : Fin m → Fin n)
    (rel : TypedRelation types) :
    TypedRelation (fun j => types (indices j)) := {
  labels := fun j => rel.labels (indices j),
  -- 'image' ('' operator) applies the function to every element in the set
  rows   := (fun t j => t (indices j)) '' rel.rows
}

@[simp]
def typedColumn {n : Nat} {types : Fin n → Type}[∀ a, DecidableEq (types a)] {α : Type}
    (index : Fin n) (rel : TypedRelation types) (h : types index = α := by simp) : Set α :=
  (fun tuple => h ▸ tuple index) '' rel.rows -- '' is for Set Image

-- Restriction / Selection
@[simp]
def restriction {n : Nat} {types : Fin n → Type}[∀ a, DecidableEq (types a)]
    (condition : (i : Fin n) → types i → Bool)
    (rel : TypedRelation types) : TypedRelation types :=
  {
    labels := rel.labels,
    rows   := { t | t ∈ rel.rows ∧ (∀ i, condition i (t i)) }
  }

-- Union (Set Union)
@[simp]
def union {n : Nat} {types : Fin n → Type}[∀ a, DecidableEq (types a)] (r1 r2 : TypedRelation types) : TypedRelation types :=
  {
    labels := r1.labels,
    rows   := r1.rows ∪ r2.rows
  }

-- Intersection
@[simp]
def intersection {n : Nat} {types : Fin n → Type}[∀ a, DecidableEq (types a)] (r1 r2 : TypedRelation types) : TypedRelation types :=
  {
    labels := r1.labels,
    rows   := r1.rows ∩ r2.rows
  }

@[simp]
def minus {n : Nat} {types : Fin n → Type}[∀ a, DecidableEq (types a)] (r1 r2 : TypedRelation types) : TypedRelation types :=
  { labels := r1.labels, rows := r1.rows \ r2.rows } -- Set Difference

/-! ## Theorems -/


/-
## Theorem: Projection Composition Law
π_A(π_B(R)) = π_{A ∘ B}(R)
-/
theorem projection_compose {n m p : Nat} {types : Fin n → Type}[∀ a, DecidableEq (types a)]
    (indices1 : Fin m → Fin n) (indices2 : Fin p → Fin m)
    (rel : TypedRelation types) :
    projection indices2 (projection indices1 rel) =
    projection (fun j => indices1 (indices2 j)) rel := by
  simp only [projection]
  grind

theorem projection_card {m : Nat} {types : Fin n → Type}[∀ a, DecidableEq (types a)] (indices : Fin m → Fin n)
    (rel : TypedRelation types) :
    (projection indices rel).rows.ncard = rel.rows.ncard := by
  simp [projection]
  sorry

theorem restriction_length_le {types : Fin n → Type}[∀ a, DecidableEq (types a)]
    (condition : (i : Fin n) → types i → Bool) (rel : TypedRelation types) :
    (restriction condition rel).rows.ncard ≤ rel.rows.ncard := by
  simp only [restriction]
  sorry


end LeanDatabase
