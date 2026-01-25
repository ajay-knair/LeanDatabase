import LeanDatabase.TypedRelation

namespace Multiset
variable {α : Type} [LinearOrder α]
instance instMinEqOr : Std.MinEqOr α where
  min_eq_or := min_choice

omit [LinearOrder α] in
@[grind .]
theorem list_perm_eq_nil_iff_nil (a b : List α) (h_ab: a ≈ b) : a = [] ↔ b = []:= by
  apply Iff.intro
  intro h_a
  rw [h_a] at h_ab
  change [].Perm b at h_ab
  rw [b.nil_perm] at h_ab
  exact h_ab
  intro h_b
  rw [h_b] at h_ab
  change a.Perm [] at h_ab
  simp at h_ab
  exact h_ab

--used Aristotle to get this
theorem perm_min? {α : Type u} [LinearOrder α] (a b : List α) (h : List.Perm a b) : List.min? a = List.min? b := by
  induction' h with a b c ha hb hc ih ; aesop;
  · cases b <;> cases c <;> aesop;
  · simp +decide [ List.min? ] ;
    rw [ min_comm ];
  · grind

def min? [LinearOrder α] (s : Multiset α) : Option α := Quotient.liftOn s List.min? (by exact perm_min?)

omit [LinearOrder α] in
lemma min?_eq_none_iff_empty [LinearOrder α] (s : Multiset α) :
    min? s = none ↔ s.card = 0 := by
  induction' s using Quotient.inductionOn with l
  apply Iff.intro
  · intro h
    simp_all
    exact List.min?_eq_none_iff.mp h
  · intro h
    simp at h
    exact List.min?_eq_none_iff.mpr h

omit [LinearOrder α] in
theorem min?_mem [inst: LinearOrder α] (s: Multiset α) : s.min? = some m → m ∈ s := by
  induction' s using Quotient.inductionOn with l
  intro h
  simp_all
  apply @List.min?_mem α m (inst.toMin) (instMinEqOr) l
  exact h

def min' [LinearOrder α] (s : Multiset α) (h : s.card > 0) : α :=
  have h: min? s ≠ none := by grind [min?_eq_none_iff_empty]
  match h_eq :min? s with
  | some m => m
  | none   => by contradiction


omit [LinearOrder α] in
theorem min'_mem [LinearOrder α] (s : Multiset α) (h : s.card > 0) : min' s h ∈ s := by
  unfold min'
  grind [min?_mem]

def toListSorted [LinearOrder α] (s : Multiset α) : List α :=
  if h : s.card > 0 then
    let m := s.min' h
    m :: toListSorted (s.erase m)
  else []
termination_by s.card
decreasing_by
  refine card_erase_lt_of_mem ?_
  apply min'_mem

end Multiset

namespace LeanDatabase




variable {n : Nat}

variable {types : Fin n → Type} [∀ i, DecidableEq (types i)][ ∀ i, LinearOrder (types i)]

-- Convert List-Relation to Multiset-Relation
@[simp, grind .]
def toMultisetRelation(r : TypedListRelation types) : TypedRelation types :=
  {
    labels := r.labels,
    rows   := r.rows
  }

def toListRelation (r : TypedRelation types) : TypedListRelation types :=
  {
    labels := r.labels
    rows   := r.rows.toListSorted
  }


omit [(i : Fin n) → LinearOrder (types i)] [(i : Fin n) → DecidableEq (types i)] in
theorem permutation_implies_multiset_equality
    (l1 l2 : TypedListRelation types) :
    l1.labels = l2.labels →
    List.Perm l1.rows l2.rows →
    toMultisetRelation l1 = toMultisetRelation l2 := by
  intro h_labels h_perm
  simp only [toMultisetRelation]
  refine TypedRelation.ext_iff.mpr ?_
  apply And.intro
  · grind
  · exact Multiset.coe_eq_coe.mpr h_perm

def projection' {m : Nat} (indices : Fin m → Fin n) (rel : TypedListRelation types) :
  TypedListRelation (fun j ↦ types (indices j)) :=
  let _ : ∀ j, DecidableEq (types (indices j)) := fun _ => inferInstance
  {
    labels := fun j => rel.labels (indices j),
    rows   := (rel.rows.map (fun t j => t (indices j))) --dedup to keep it same as Finset version
  }

def restriction' (predicate : TypedTuple types → Bool) (rel : TypedListRelation types) :
    TypedListRelation types :=
  {
    labels := rel.labels,
    rows   := rel.rows.filter (fun t => predicate t)
  }

def union' (r1 r2 : TypedListRelation types) : TypedListRelation types :=
  {
    labels := r1.labels,
    rows   := r1.rows ++ r2.rows -- Finset Union
  }

@[simp, grind]
def intersection' (r1 r2 : TypedListRelation types) : TypedListRelation types :=
  {
    labels := r1.labels,
    rows   := r1.rows.filter (fun t => r2.rows.contains t) -- O (|r1|*|r2|)
  }

-- Intersect sorted lists if this is slow

@[simp, grind]
def minus' (r1 r2 : TypedListRelation types) : TypedListRelation types :=
  {
    labels := r1.labels,
    rows   := r1.rows.filter (fun t => ¬ r2.rows.contains t) -- O (|r1|*|r2|)
  }
-- Again explore sorted lists if this is slow

@[simp, grind]
def rename' (newLabels : Fin n → String) (rel : TypedListRelation types) : TypedListRelation types :=
  {
    labels := newLabels,
    rows   := rel.rows
  }

def renameColumn' (idx : Fin n) (newName : String) (rel : TypedListRelation types) : TypedListRelation types :=
  {
    labels := Function.update rel.labels idx newName,
    rows   := rel.rows
  }

@[simp]
def prefixLabels' (prefixStr : String) (rel : TypedListRelation types) : TypedListRelation types :=
  {
    labels := fun i => prefixStr ++ "." ++ rel.labels i,
    rows   := rel.rows
  }

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
/-Theorems-/
omit [(i : Fin n) → LinearOrder (types i)] in
theorem projection_compose' {m p : Nat}
    (indices1 : Fin m → Fin n) (indices2 : Fin p → Fin m)
    (rel : TypedListRelation types) :
    projection' indices2 (projection' indices1 rel) =
    projection' (fun j ↦ indices1 (indices2 j)) rel := by
    simp only [projection']
    apply TypedListRelation.ext
    · simp only
    · simp only
      have := dedup_map_dedup_eq (fun t j ↦ t (indices2 j)) (List.map (fun t j ↦ t (indices1 j)) rel.rows)
      simp only [List.map_map]; congr

omit [(i : Fin n) → LinearOrder (types i)] in
theorem projection'_length_le {m : Nat} (indices : Fin m → Fin n)
    (rel : TypedListRelation types) :
    (projection' indices rel).rows.length ≤ rel.rows.length := by
    simp only [projection']
    have : (List.map (fun t j ↦ t (indices j)) rel.rows).length = rel.rows.length := by
      simp only [List.length_map]
    rw [← this]

omit [(i : Fin n) → DecidableEq (types i)] [(i : Fin n) → LinearOrder (types i)] in
theorem restriction'_length_le
    (predicate : TypedTuple types → Bool) (rel : TypedListRelation types) :
    (restriction' predicate rel).rows.length ≤ rel.rows.length := by
    simp only [restriction', List.length_filter_le ]
