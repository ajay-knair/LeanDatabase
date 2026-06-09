import LeanDatabase.CurriedPredicates

namespace LeanDatabase

namespace ListRelation

variable {n : Nat}
variable {colType : Fin n → Type} [∀ i, DecidableEq (colType i)][ ∀ i, LinearOrder (colType i)]

@[ext, grind] structure TypedListRelation (colType : Fin n → Type) where
  labels : Fin n → String
  rows   : List (TypedTuple colType)
deriving Inhabited

-- Define the Equivalence Logic
@[simp, grind .]
def equivalent (r1 r2 : TypedListRelation colType) : Prop :=
  r1.labels = r2.labels ∧ List.Perm r1.rows r2.rows

infix:50 " ~ " => equivalent

instance : Setoid (TypedListRelation colType) where
  r := equivalent
  iseqv := {
    refl  := fun _ => ⟨rfl, List.Perm.refl _⟩
    symm  := fun ⟨hL, hR⟩ => ⟨hL.symm, List.Perm.symm hR⟩
    trans := fun ⟨hL1, hR1⟩ ⟨hL2, hR2⟩ => ⟨hL1.trans hL2, List.Perm.trans hR1 hR2⟩
  }

@[simp, grind .]
def emptyListRel (l : Fin n → String) : TypedListRelation colType :=
  { labels := l, rows := [] }

-- Convert List-Relation to Finset-Relation
@[simp, grind .]
def toFinsetRelation (r : TypedListRelation colType) : TypedRelation colType :=
  {
    labels := r.labels,
    rows   := r.rows.toFinset
  }

def toListRelation (r : TypedRelation colType) : TypedListRelation colType :=
  {
    labels := r.labels
    rows   := r.rows.toListSorted
  }

omit [(i : Fin n) → LinearOrder (colType i)] in
theorem permutation_implies_finset_equality
    (l1 l2 : TypedListRelation colType) :
    l1.labels = l2.labels →
    List.Perm l1.rows l2.rows →
    toFinsetRelation l1 = toFinsetRelation l2 := by
  intro h_labels h_perm
  grind only [toFinsetRelation, List.toFinset_eq_of_perm]

/-! ## Relational Algebra Operations on Lists -/

@[simp]
def projection {m : Nat} (indices : Fin m → Fin n) (rel : TypedListRelation colType) :
  TypedListRelation (fun j ↦ colType (indices j)) :=
  let _ : ∀ j, DecidableEq (colType (indices j)) := fun _ => inferInstance
  {
    labels := fun j => rel.labels (indices j),
    rows   := (rel.rows.map (fun t j => t (indices j))).dedup --dedup to keep it same as Finset version
  }

def restriction (predicate : TypedTuple colType → Bool) (rel : TypedListRelation colType) :
    TypedListRelation colType :=
  {
    labels := rel.labels,
    rows   := rel.rows.filter (fun t => predicate t)
  }

def restrictionCurried (p: curriedPred (cols := colType)) (rel: TypedListRelation colType) : TypedListRelation colType :=
{
  labels := rel.labels,
  rows := rel.rows.filter (fun t => applyCurried p t)
}

-- Union
def union (r1 r2 : TypedListRelation colType) : TypedListRelation colType :=
  {
    labels := r1.labels,
    rows   := r1.rows ++ r2.rows -- Finset Union
  }

-- Intersection
@[simp, grind]
def intersection (r1 r2 : TypedListRelation colType) : TypedListRelation colType :=
  {
    labels := r1.labels,
    rows := r1.rows.bagInter r2.rows -- O (|r1|*|r2|)
  }

-- Minus / Difference
@[simp, grind]
def minus (r1 r2 : TypedListRelation colType) : TypedListRelation colType :=
  {
    labels := r1.labels,
    rows   := r1.rows.diff r2.rows
  }


-- RENAME operator: Changes labels, keeps data exactly the same.
@[simp, grind]
def rename (newLabels : Fin n → String) (rel : TypedListRelation colType) : TypedListRelation colType :=
  {
    labels := newLabels,
    rows   := rel.rows
  }

-- Helper: Rename a specific column by index
def renameColumn (idx : Fin n) (newName : String) (rel : TypedListRelation colType) : TypedListRelation colType :=
  {
    labels := Function.update rel.labels idx newName,
    rows   := rel.rows
  }

-- Helper to prefix all labels in a relation, useful for cross product
@[simp]
def prefixLabels (prefixStr : String) (rel : TypedListRelation colType) : TypedListRelation colType :=
  {
    labels := fun i => prefixStr ++ "." ++ rel.labels i,
    rows   := rel.rows
  }

/-! ## Theorems -/

lemma dedup_map_dedup_eq {α β} [DecidableEq α] [DecidableEq β]
    (f : α → β) (l : List α) : (l.dedup.map f).dedup = (l.map f).dedup := by
    induction l with
    | nil => simp only [List.dedup_nil, List.map_nil]
    | cons x xs ih =>
      simp only [List.dedup_cons, List.map_cons]
      split_ifs with h₁ h₂ h₂
      -- x ∈ xs and f x ∈ f xs
      · exact ih
      -- x ∈ xs but f x ∉ f xs
      · exfalso; grind only [List.mem_map]
      -- x ∉ xs but f x ∈ f xs
      · have : f x ∈ List.map f xs.dedup := by
          grind only [List.mem_map, List.mem_dedup]
        simp only [List.map_cons, this, List.dedup_cons_of_mem, ih]
      -- x ∉ xs and f x ∉ f xs
      · simp only [List.dedup_cons, List.map_cons, ih]
        have : f x ∉ List.map f xs.dedup := by
          grind only [List.mem_map, List.mem_dedup]
        simp only [this, ↓reduceIte]

omit [(i : Fin n) → LinearOrder (colType i)] in
theorem projection_compose {m p : Nat}
    (indices1 : Fin m → Fin n) (indices2 : Fin p → Fin m)
    (rel : TypedListRelation colType) :
    projection indices2 (projection indices1 rel) =
    projection (fun j ↦ indices1 (indices2 j)) rel := by
    simp only [projection]
    apply TypedListRelation.ext
    · simp only
    · simp only
      have := dedup_map_dedup_eq (fun t j ↦ t (indices2 j)) (List.map (fun t j ↦ t (indices1 j)) rel.rows)
      rw [this]; congr 1
      simp only [List.map_map]; congr

-- Projection removes duplicates, so size is <= original, not equal.
omit [(i : Fin n) → LinearOrder (colType i)] in
theorem projection_length_le {m : Nat} (indices : Fin m → Fin n)
    (rel : TypedListRelation colType) :
    (projection indices rel).rows.length ≤ rel.rows.length := by
    simp only [projection]
    have : (List.map (fun t j ↦ t (indices j)) rel.rows).length = rel.rows.length := by
      simp only [List.length_map]
    rw [← this]
    apply List.Sublist.length_le
    apply List.dedup_sublist

-- Theorem: Restriction Cardinality
-- |σ(R)| ≤ |R|
-- "Filtering rows can never increase the number of rows."
omit [(i : Fin n) → DecidableEq (colType i)] [(i : Fin n) → LinearOrder (colType i)] in
theorem restriction_length_le
    (predicate : TypedTuple colType → Bool) (rel : TypedListRelation colType) :
    (restriction predicate rel).rows.length ≤ rel.rows.length := by
    simp only [restriction, List.length_filter_le ]

omit [(i : Fin n) → DecidableEq (colType i)] [(i : Fin n) → LinearOrder (colType i)] in
theorem restrictionCurried_card_le
    (p : curriedPred (cols := colType))(rel : TypedListRelation colType) :
    (restrictionCurried p rel).rows.length ≤ rel.rows.length:= by
  simp only [restrictionCurried, List.length_filter_le]

end ListRelation
end LeanDatabase
