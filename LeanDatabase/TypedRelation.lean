import Mathlib

namespace Finset

-- Maybe Finset.sort is equivalent to this
def toListSorted [LinearOrder α] (s : Finset α) : List α :=
  if h : s.Nonempty then
    let m := s.min' h
    m :: toListSorted (s.erase m)
  else []
termination_by s.card
decreasing_by
  apply Finset.card_erase_lt_of_mem
  apply Finset.min'_mem
end Finset

namespace LeanDatabase

variable {n : Nat}

/-!
## Typed Relations (Finset Definition)

We use `Finset` (Finite Sets) which allows us to compute cardinality
and guarantees finiteness, unlike `Set`. Our Databases are also finite
so this will help us in future.
-/

-- Finsets require Decidable Equality to handle deduplication
variable {colType : Fin n → Type} [∀ i, DecidableEq (colType i)][ ∀ i, LinearOrder (colType i)]
abbrev  TypedTuple (colType : Fin n → Type) := (i : Fin n) → colType i

-- We ensure tuples can be compared for equality
instance : DecidableEq (TypedTuple colType) :=
  inferInstanceAs (DecidableEq ((i : Fin n) → colType i))

-- Pi.Lex.linearOrder is noncomputable, hence the manual approach to Lexicographic ordering
-- noncomputable instance [inst : ∀ i, LinearOrder (colType i)] : LinearOrder (TypedTuple colType) :=
--   @Pi.Lex.linearOrder (Fin n) colType _ _ inst

variable (r s t : TypedTuple colType)
set_option linter.unusedSectionVars false

theorem eq_iff : r = s ↔ ∀ i, r i = s i := by grind only

def lt : Prop := ∃ i : Fin n, (r i < s i) ∧ (∀ j : Fin n, j < i → r j = s j)
instance : LT (TypedTuple colType) := ⟨lt⟩
instance : Decidable (lt r s) := by unfold lt; infer_instance
instance : Decidable (r < s) := inferInstanceAs (Decidable (lt r s))
instance : DecidableLT (TypedTuple colType) := by infer_instance

-- @[simp, grind =]
theorem lt_iff : r < s ↔ ∃ i : Fin n, (r i < s i) ∧ (∀ j : Fin n, j < i → r j = s j) := by rfl

def le : Prop := r < s ∨ r = s
instance : LE (TypedTuple colType) := ⟨le⟩
instance : Decidable (le r s) := by unfold le; infer_instance
instance : Decidable (r ≤ s) := inferInstanceAs (Decidable (le r s))
instance : DecidableLE (TypedTuple colType) := by infer_instance


theorem le_iff : r ≤ s ↔ r < s ∨ r = s := by rfl

def min := if r ≤ s then r else s
def max := if r ≤ s then s else r

theorem le_refl : r ≤ r := by grind only [le_iff]

theorem lt_trans : r < s → s < t → r < t := by
  simp only [lt_iff]; intro ⟨i₁, h₁, h_eq₁⟩ ⟨i₂, h₂, h_eq₂⟩
  rcases lt_trichotomy i₁ i₂ with h | h | h
  · use i₁; constructor
    · specialize h_eq₂ i₁ h; rw [← h_eq₂]; exact h₁
    · grind only
  · use i₁; rw [← h] at h₂ h_eq₂; constructor
    · exact _root_.lt_trans h₁ h₂
    · grind only
  · grind only

theorem le_trans : r ≤ s → s ≤ t → r ≤ t := by
  simp only [le_iff]; intro h₁ h₂
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> grind only [lt_trans]

theorem not_gt_of_lt : r < s → ¬s < r := by
  simp only [lt_iff, not_exists, not_and, not_forall]
  intro ⟨j, hj, h_eq⟩ i hi --; obtain ⟨j, hj, h_eq⟩ := h
  have : j < i := by
          by_contra h
          rcases (not_lt_iff_eq_or_lt.mp h) with h | h
          · rw [h] at hj; grind only
          · specialize h_eq i h; grind only
  use j, this; grind only

theorem not_eq_of_lt : r < s → ¬ r = s := by grind only [lt_iff]

theorem lt_iff_le_not_ge : r < s ↔ r ≤ s ∧ ¬s ≤ r := by
  constructor
  · intro h; constructor
    · left; exact h
    · rw [le_iff, not_or]
      constructor <;> grind only [not_gt_of_lt, not_eq_of_lt]
  · intro h; simp only [le_iff, not_or] at h
    grind only

theorem le_antisymm : r ≤ s → s ≤ r → r = s := by
  simp only [le_iff]; intro h₁ h₂
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> grind only [lt_iff_le_not_ge, le_iff]

theorem exists_first_diff (h : ¬ r = s) : ∃ i, ¬ r i = s i ∧ ∀ j < i, r j = s j := by
  let p : Fin n → Bool := fun i ↦ r i ≠ s i
  match h_find : Fin.find? p with
  | none =>
    simp only [ne_eq, decide_not, Fin.findSome?_eq_none_iff, Option.guard_eq_none_iff,
      Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq, p, ← eq_iff] at h_find
    exfalso; grind only
  | some i =>
    simp only [ne_eq, decide_not, Fin.findSome?_eq_some_iff, Option.guard_eq_some_iff,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Option.guard_eq_none_iff,
      Bool.not_false, decide_eq_true_eq, ↓existsAndEq, true_and, p] at h_find
    use i

theorem le_total : r ≤ s ∨ s ≤ r := by
  if h : r = s then grind only [le_iff]
  else
    simp only [le_iff, h, or_false]; rw [eq_comm] at h
    simp only [h, or_false]; rw [eq_comm] at h
    obtain ⟨i, hi, hi'⟩ := exists_first_diff _ _ h
    rcases Ne.lt_or_gt hi <;> grind only [lt_iff]

instance  [inst : ∀ i, LinearOrder (colType i)] : LinearOrder (TypedTuple colType) where
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm
  le_total := le_total
  toDecidableLE := by infer_instance
  lt_iff_le_not_ge := lt_iff_le_not_ge
  min := fun a b => if a ≤ b then a else b
  max := fun a b => if a ≤ b then b else a
  min_def := by intros; rfl
  max_def := by intros; rfl


/-! ## Definitions -/

@[ext, grind cases] structure TypedRelation (colType : Fin n → Type) [∀ i, DecidableEq (colType i)] where
  labels : Fin n → String
  rows   : Finset (TypedTuple colType)
deriving Inhabited

-- Definition of an Empty Relation (The "Zero" element)
def emptyRel (l : Fin n → String) : TypedRelation colType :=
  { labels := l, rows := ∅ }

/-! ## Relational Algebra Operations on Finsets -/

-- Projection (uses Finset.image)
@[simp]
def projection {m : Nat} (indices : Fin m → Fin n) (rel : TypedRelation colType) :
    TypedRelation (fun j => colType (indices j)) :=

  let _ : ∀ j, DecidableEq (colType (indices j)) := fun _ => inferInstance
  {
    labels := fun j => rel.labels (indices j),
    rows   := rel.rows.image (fun t j => t (indices j))
  }

@[simp]
def typedColumn {α : Type} [DecidableEq α]
    (index : Fin n) (rel : TypedRelation colType) (h : colType index = α := by simp) : Finset α :=
  -- Cast the tuple value to alpha and image it
  rel.rows.image (fun tuple => h ▸ tuple index)

-- Restriction (uses Finset.filter)
@[simp, grind]
def restriction (predicate : TypedTuple colType → Bool) (rel : TypedRelation colType) :
    TypedRelation colType :=
  {
    labels := rel.labels,
    rows   := rel.rows.filter (fun t => predicate t)
  }

-- Selection is same as restriction, but is also commonly used
def selection (predicate : TypedTuple colType → Bool) (rel : TypedRelation colType) :
    TypedRelation colType :=
  restriction predicate rel

-- Union
@[simp, grind]
def union (r1 r2 : TypedRelation colType) : TypedRelation colType :=
  {
    labels := r1.labels,
    rows   := r1.rows ∪ r2.rows -- Finset Union
  }

-- Intersection
@[simp, grind]
def intersection (r1 r2 : TypedRelation colType) : TypedRelation colType :=
  {
    labels := r1.labels,
    rows   := r1.rows ∩ r2.rows -- Finset Intersection
  }

-- Minus / Difference
@[simp, grind]
def minus (r1 r2 : TypedRelation colType) : TypedRelation colType :=
  {
    labels := r1.labels,
    rows   := r1.rows \ r2.rows -- Finset Difference (sdiff)
  }

-- RENAME operator: Changes labels, keeps data exactly the same.
@[simp, grind]
def rename (newLabels : Fin n → String) (rel : TypedRelation colType) : TypedRelation colType :=
  {
    labels := newLabels,
    rows   := rel.rows
  }

-- Helper: Rename a specific column by index
def renameColumn (idx : Fin n) (newName : String) (rel : TypedRelation colType) : TypedRelation colType :=
  {
    labels := Function.update rel.labels idx newName,
    rows   := rel.rows
  }

-- Helper to prefix all labels in a relation, useful for cross product
@[simp]
def prefixLabels (prefixStr : String) (rel : TypedRelation colType) : TypedRelation colType :=
  {
    labels := fun i => prefixStr ++ "." ++ rel.labels i,
    rows   := rel.rows
  }
/-
@[simp]
def prefixLabels' (prefixStr : String) (rel : TypedListRelation colType) : TypedListRelation colType :=
  {
    labels := fun i => prefixStr ++ "." ++ rel.labels i,
    rows   := rel.rows
  }
-/

/-! ## Theorems -/

theorem projection_compose {m p : Nat}
    (indices1 : Fin m → Fin n) (indices2 : Fin p → Fin m)
    (rel : TypedRelation colType) :
    projection indices2 (projection indices1 rel) =
    projection (fun j => indices1 (indices2 j)) rel := by
  simp only [projection]
  apply TypedRelation.ext
  · simp only
  · simp only [Finset.image_image]
    grind

-- Projection removes duplicates, so size is <= original, not equal.
theorem projection_card_le {m : Nat} (indices : Fin m → Fin n)
    (rel : TypedRelation colType) :
    (projection indices rel).rows.card ≤ rel.rows.card := by
  simp only [projection]
  -- Law: |image f S| ≤ |S|
  apply Finset.card_image_le

-- Theorem: Restriction Cardinality
-- |σ(R)| ≤ |R|
-- "Filtering rows can never increase the number of rows."
theorem restriction_card_le
    (predicate : TypedTuple colType → Bool) (rel : TypedRelation colType) :
    (restriction predicate rel).rows.card ≤ rel.rows.card := by
  simp only [restriction]
  -- |filter p S| ≤ |S|
  apply Finset.card_filter_le

/-
omit [(i : Fin n) → DecidableEq (colType i)] [(i : Fin n) → LinearOrder (colType i)] in
theorem restriction'_length_le
    (predicate : TypedTuple colType → Bool) (rel : TypedListRelation colType) :
    (restriction' predicate rel).rows.length ≤ rel.rows.length := by
    simp only [restriction', List.length_filter_le ]
-/
/-
### Formatting to print
-/

-- format a single tuple to: "[Val1, Val2, ...]"
def formatTuple [∀ i, ToString (colType i)] (t : TypedTuple colType) : String :=
  let parts := List.finRange n |>.map (fun i => toString (t i))
  "[" ++ (String.intercalate ", " parts) ++ "]"

-- Helper to format the whole table
-- Note: We use 'unsafe' to convert the Set of rows into a List for printing
unsafe def simpleFormat [∀ i, DecidableEq (colType i)] [∀ i, ToString (colType i)]
    (rel : TypedRelation colType) : String :=
  let labelStr := "Labels: " ++ toString (List.ofFn rel.labels)

  -- unsafeCast allows us to view the Set as a List just for printing
  let rowList : List (TypedTuple colType) := unsafeCast rel.rows.val
  let rowStrs := rowList.map (fun r => "Row:    " ++ formatTuple r)

  String.intercalate "\n" (labelStr :: rowStrs)

unsafe instance [∀ i, DecidableEq (colType i)] [∀ i, ToString (colType i)] :
    Repr (TypedRelation colType) where
  reprPrec rel _ := simpleFormat rel
