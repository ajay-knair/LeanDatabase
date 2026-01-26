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
variable {types : Fin n → Type} [∀ i, DecidableEq (types i)][ ∀ i, LinearOrder (types i)]
abbrev TypedTuple (types : Fin n → Type) := (i : Fin n) → types i

-- We ensure tuples can be compared for equality
instance : DecidableEq (TypedTuple types) :=
  inferInstanceAs (DecidableEq ((i : Fin n) → types i))

-- Pi.Lex.linearOrder is noncomputable, hence the manual approach to Lexicographic ordering
-- noncomputable instance [inst : ∀ i, LinearOrder (types i)] : LinearOrder (TypedTuple types) :=
--   @Pi.Lex.linearOrder (Fin n) types _ _ inst

variable (r s t : TypedTuple types)


omit [(i : Fin n) → DecidableEq (types i)] [(i : Fin n) → LinearOrder (types i)] in
theorem eq_iff : r = s ↔ ∀ i, r i = s i := by grind only

@[simp, grind .]
def lt : Prop := ∃ i : Fin n, (r i < s i) ∧ (∀ j : Fin n, j < i → r j = s j)
instance : LT (TypedTuple types) := ⟨lt⟩
instance : Decidable (lt r s) := by unfold lt; infer_instance
instance : Decidable (r < s) := inferInstanceAs (Decidable (lt r s))
instance : DecidableLT (TypedTuple types) := by infer_instance

-- @[simp, grind =]
omit [(i : Fin n) → DecidableEq (types i)] in
theorem lt_iff : r < s ↔ ∃ i : Fin n, (r i < s i) ∧ (∀ j : Fin n, j < i → r j = s j) := by rfl

@[simp, grind .]
def le : Prop := r < s ∨ r = s
instance : LE (TypedTuple types) := ⟨le⟩
instance : Decidable (le r s) := by unfold le; infer_instance
instance : Decidable (r ≤ s) := inferInstanceAs (Decidable (le r s))
instance : DecidableLE (TypedTuple types) := by infer_instance


omit [(i : Fin n) → DecidableEq (types i)] in
@[simp, grind =] theorem le_iff : r ≤ s ↔ r < s ∨ r = s := by rfl

def min := if r ≤ s then r else s
def max := if r ≤ s then s else r

omit [(i : Fin n) → DecidableEq (types i)] in
@[simp, grind .] theorem le_refl : r ≤ r := by grind only [le_iff]

omit [(i : Fin n) → DecidableEq (types i)] in
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

omit [(i : Fin n) → DecidableEq (types i)] in
@[simp, grind .] theorem le_trans : r ≤ s → s ≤ t → r ≤ t := by
  simp only [le_iff]; intro h₁ h₂
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> grind only [lt_trans]

omit [(i : Fin n) → DecidableEq (types i)] in
theorem not_gt_of_lt : r < s → ¬s < r := by
  simp only [lt_iff, not_exists, not_and, not_forall]
  intro ⟨j, hj, h_eq⟩ i hi --; obtain ⟨j, hj, h_eq⟩ := h
  have : j < i := by
          by_contra h
          rcases (not_lt_iff_eq_or_lt.mp h) with h | h
          · rw [h] at hj; grind only
          · specialize h_eq i h; grind only
  use j, this; grind only

omit [(i : Fin n) → DecidableEq (types i)] in
theorem not_eq_of_lt : r < s → ¬ r = s := by grind only [lt_iff]

omit [(i : Fin n) → DecidableEq (types i)] in
@[simp, grind .] theorem lt_iff_le_not_ge : r < s ↔ r ≤ s ∧ ¬s ≤ r := by
  constructor
  · intro h; constructor
    · left; exact h
    · rw [le_iff, not_or]
      constructor <;> grind only [not_gt_of_lt, not_eq_of_lt]
  · intro h; simp only [le_iff, not_or] at h
    grind only

omit [(i : Fin n) → DecidableEq (types i)] in
@[simp, grind .] theorem le_antisymm : r ≤ s → s ≤ r → r = s := by
  simp only [le_iff]; intro h₁ h₂
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> grind only [lt_iff_le_not_ge, le_iff]

omit [(i : Fin n) → LinearOrder (types i)] in
@[simp] theorem exists_first_diff (h : ¬ r = s) : ∃ i, ¬ r i = s i ∧ ∀ j < i, r j = s j := by
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

@[simp, grind .] theorem le_total : r ≤ s ∨ s ≤ r := by
  if h : r = s then grind only [le_iff]
  else
    simp only [le_iff, h, or_false]; rw [eq_comm] at h
    simp only [h, or_false]; rw [eq_comm] at h
    obtain ⟨i, hi, hi'⟩ := exists_first_diff _ _ h
    rcases Ne.lt_or_gt hi <;> grind only [lt_iff]

instance  [inst : ∀ i, LinearOrder (types i)] : LinearOrder (TypedTuple types) where
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

def emptyListRel (l : Fin n → String) : TypedListRelation types :=
  { labels := l, rows := [] }

-- Convert List-Relation to Finset-Relation
@[simp, grind .]
def toFinsetRelation (r : TypedListRelation types) : TypedRelation types :=
  {
    labels := r.labels,
    rows   := r.rows.toFinset
  }

def toListRelation (r : TypedRelation types) : TypedListRelation types :=
  {
    labels := r.labels
    rows   := r.rows.toListSorted
  }

omit [(i : Fin n) → LinearOrder (types i)] in
theorem permutation_implies_finset_equality
    (l1 l2 : TypedListRelation types) :
    l1.labels = l2.labels →
    List.Perm l1.rows l2.rows →
    toFinsetRelation l1 = toFinsetRelation l2 := by
  intro h_labels h_perm
  grind only [toFinsetRelation, List.toFinset_eq_of_perm]
  -- simp_all [toFinsetRelation]
  -- exact List.toFinset_eq_of_perm l1.rows l2.rows h_perm

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
def projection' {m : Nat} (indices : Fin m → Fin n) (rel : TypedListRelation types) :
  TypedListRelation (fun j ↦ types (indices j)) :=
  let _ : ∀ j, DecidableEq (types (indices j)) := fun _ => inferInstance
  {
    labels := fun j => rel.labels (indices j),
    rows   := (rel.rows.map (fun t j => t (indices j))).dedup --dedup to keep it same as Finset version
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

def restriction' (predicate : TypedTuple types → Bool) (rel : TypedListRelation types) :
    TypedListRelation types :=
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

def union' (r1 r2 : TypedListRelation types) : TypedListRelation types :=
  {
    labels := r1.labels,
    rows   := r1.rows ++ r2.rows -- Finset Union
  }

-- Intersection
@[simp, grind]
def intersection (r1 r2 : TypedRelation types) : TypedRelation types :=
  {
    labels := r1.labels,
    rows   := r1.rows ∩ r2.rows -- Finset Intersection
  }

@[simp, grind]
def intersection' (r1 r2 : TypedListRelation types) : TypedListRelation types :=
  {
    labels := r1.labels,
    rows   := r1.rows.filter (fun t => r2.rows.contains t) -- O (|r1|*|r2|)
  }
-- Intersect sorted lists if this is slow

-- Minus / Difference
@[simp, grind]
def minus (r1 r2 : TypedRelation types) : TypedRelation types :=
  {
    labels := r1.labels,
    rows   := r1.rows \ r2.rows -- Finset Difference (sdiff)
  }

@[simp, grind]
def minus' (r1 r2 : TypedListRelation types) : TypedListRelation types :=
  {
    labels := r1.labels,
    rows   := r1.rows.filter (fun t => ¬ r2.rows.contains t) -- O (|r1|*|r2|)
  }
-- Again explore sorted lists if this is slow


-- RENAME operator: Changes labels, keeps data exactly the same.
@[simp, grind]
def rename (newLabels : Fin n → String) (rel : TypedRelation types) : TypedRelation types :=
  {
    labels := newLabels,
    rows   := rel.rows
  }

@[simp, grind]
def rename' (newLabels : Fin n → String) (rel : TypedListRelation types) : TypedListRelation types :=
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

def renameColumn' (idx : Fin n) (newName : String) (rel : TypedListRelation types) : TypedListRelation types :=
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

@[simp]
def prefixLabels' (prefixStr : String) (rel : TypedListRelation types) : TypedListRelation types :=
  {
    labels := fun i => prefixStr ++ "." ++ rel.labels i,
    rows   := rel.rows
  }


/-! ## Theorems -/

omit [(i : Fin n) → LinearOrder (types i)] in
theorem projection_compose {m p : Nat}
    (indices1 : Fin m → Fin n) (indices2 : Fin p → Fin m)
    (rel : TypedRelation types) :
    projection indices2 (projection indices1 rel) =
    projection (fun j => indices1 (indices2 j)) rel := by
  simp only [projection]
  apply TypedRelation.ext
  · simp only
  · simp only [Finset.image_image]
    grind

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

omit [(i : Fin n) → LinearOrder (types i)] in
theorem prejection_compose' {m p : Nat}
    (indices1 : Fin m → Fin n) (indices2 : Fin p → Fin m)
    (rel : TypedListRelation types) :
    projection' indices2 (projection' indices1 rel) =
    projection' (fun j ↦ indices1 (indices2 j)) rel := by
    simp only [projection']
    apply TypedListRelation.ext
    · simp only
    · simp only
      have := dedup_map_dedup_eq (fun t j ↦ t (indices2 j)) (List.map (fun t j ↦ t (indices1 j)) rel.rows)
      rw [this]; congr 1
      simp only [List.map_map]; congr

-- Projection removes duplicates, so size is <= original, not equal.
omit [(i : Fin n) → LinearOrder (types i)] in
theorem projection_card_le {m : Nat} (indices : Fin m → Fin n)
    (rel : TypedRelation types) :
    (projection indices rel).rows.card ≤ rel.rows.card := by
  simp only [projection]
  -- Law: |image f S| ≤ |S|
  apply Finset.card_image_le

omit [(i : Fin n) → LinearOrder (types i)] in
theorem projection'_length_le {m : Nat} (indices : Fin m → Fin n)
    (rel : TypedListRelation types) :
    (projection' indices rel).rows.length ≤ rel.rows.length := by
    simp only [projection']
    have : (List.map (fun t j ↦ t (indices j)) rel.rows).length = rel.rows.length := by
      simp only [List.length_map]
    rw [← this]
    apply List.Sublist.length_le
    apply List.dedup_sublist

-- Theorem: Restriction Cardinality
-- |σ(R)| ≤ |R|
-- "Filtering rows can never increase the number of rows."
omit [(i : Fin n) → DecidableEq (types i)] [(i : Fin n) → LinearOrder (types i)] in
theorem restriction_card_le
    (predicate : TypedTuple types → Bool) (rel : TypedRelation types) :
    (restriction predicate rel).rows.card ≤ rel.rows.card := by
  simp only [restriction]
  -- |filter p S| ≤ |S|
  apply Finset.card_filter_le

omit [(i : Fin n) → DecidableEq (types i)] [(i : Fin n) → LinearOrder (types i)] in
theorem restriction'_length_le
    (predicate : TypedTuple types → Bool) (rel : TypedListRelation types) :
    (restriction' predicate rel).rows.length ≤ rel.rows.length := by
    simp only [restriction', List.length_filter_le ]

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
