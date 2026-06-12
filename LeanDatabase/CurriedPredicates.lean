import Mathlib
import LeanDatabase.TypedRelation

namespace LeanDatabase

variable {n : Nat} {colType : Fin n → Type}
variable [∀ i, DecidableEq (colType i)]

/-! ### Curried Predicates -/

def curriedPred {m : Nat} (cols : Fin m → Type) : Type :=
  match m with
  | 0   => Bool
  | k+1 => cols (0 : Fin (k+1)) → curriedPred (fun i => cols (Fin.succ i))

@[grind .]
def applyCurried {m : Nat} {cols : Fin m → Type}
    (p : curriedPred (cols := cols)) (t : (i : Fin m) → cols i) : Bool :=
  match m with
  | 0   => p
  | k+1 =>
    let p' := p (t (0 : Fin (k+1)))
    let t' : (i : Fin k) → cols (Fin.succ i) := fun i => t (Fin.succ i)
    applyCurried p' t'

@[grind .]
def restrictionCurried (rel : TypedRelation colType)
    (p : curriedPred (cols := colType)) :
    TypedRelation colType :=
  {
    labels := rel.labels,
    rows   := rel.rows.filter (fun t => applyCurried p t)
  }

def restrictionCurried'
    (rel : TypedRelation colType) (p : curriedPred (cols := colType)) :
    TypedRelation colType :=
  {
    labels := rel.labels,
    rows   := rel.rows.filter (fun t => applyCurried p t)
  }

#check restrictionCurried'

/-- `p OR q` as a curried predicate. -/
def orCurried {m : Nat} {cols : Fin m → Type}
    (p q : curriedPred (cols := cols)) : curriedPred (cols := cols) :=
  match m with
  | 0 => p || q
  | _ + 1 => fun x =>
      orCurried (cols := fun i => cols (Fin.succ i)) (p x) (q x)

/-- `p AND q` as a curried predicate. -/
def andCurried {m : Nat} {cols : Fin m → Type}
    (p q : curriedPred (cols := cols)) : curriedPred (cols := cols) :=
  match m with
  | 0 => p && q
  | _ + 1 => fun x =>
      andCurried (cols := fun i => cols (Fin.succ i)) (p x) (q x)

/-- `NOT p` as a curried predicate. -/
def notCurried {m : Nat} {cols : Fin m → Type}
    (p : curriedPred (cols := cols)) : curriedPred (cols := cols) :=
  match m with
  | 0 => !p
  | _ + 1 => fun x =>
      notCurried (cols := fun i => cols (Fin.succ i)) (p x)

theorem applyCurried_orCurried {m : Nat} {cols : Fin m → Type}
    (p q : curriedPred (cols := cols)) (t : (i : Fin m) → cols i) :
    applyCurried (orCurried p q) t = (applyCurried p t || applyCurried q t) := by
  induction m with
  | zero =>
      simp [orCurried, applyCurried]
  | succ _ ih =>
      simp [orCurried, applyCurried, ih]

theorem applyCurried_andCurried {m : Nat} {cols : Fin m → Type}
    (p q : curriedPred (cols := cols)) (t : (i : Fin m) → cols i) :
    applyCurried (andCurried p q) t = (applyCurried p t && applyCurried q t) := by
  induction m with
  | zero =>
      simp [andCurried, applyCurried]
  | succ _ ih =>
      simp [andCurried, applyCurried, ih]

theorem applyCurried_notCurried {m : Nat} {cols : Fin m → Type}
    (p : curriedPred (cols := cols)) (t : (i : Fin m) → cols i) :
    applyCurried (notCurried p) t = !applyCurried p t := by
  induction m with
  | zero =>
      simp [notCurried, applyCurried]
  | succ _ ih =>
      simp [notCurried, applyCurried, ih]

theorem restrictionCurried_card_le
    (p : curriedPred (cols := colType)) (rel : TypedRelation colType) :
    (restrictionCurried rel p).rows.card ≤ rel.rows.card := by
  simp only [restrictionCurried]
  apply Finset.card_filter_le

-- Theorem: Selection over a curried disjunctive predicate is a Union of selections
@[grind =]
theorem restriction_orCurried (p q : curriedPred (cols := colType)) (r : TypedRelation colType) :
    restrictionCurried r (orCurried p q) =
    union (restrictionCurried r p) (restrictionCurried r q) := by
  simp only [restrictionCurried, union, TypedRelation.mk.injEq, true_and]
  ext x
  simp [applyCurried_orCurried]
  grind

-- Theorem: curried version of `union_restriction_disjoint`
@[grind =]
theorem union_restrictionCurried_disjoint (p q : curriedPred (cols := colType))
    (r : TypedRelation colType) :
    union (restrictionCurried r p)
      (restrictionCurried r (andCurried q (notCurried p))) =
    restrictionCurried r (orCurried p q) := by
  simp only [restrictionCurried, union, TypedRelation.mk.injEq, true_and]
  ext x
  simp [applyCurried_orCurried, applyCurried_andCurried, applyCurried_notCurried]
  grind

-- Theorem: curried version of `restriction_inter_distrib`
theorem restrictionCurried_inter_distrib (p : curriedPred (cols := colType))
    (r1 r2 : TypedRelation colType) :
    restrictionCurried (intersection r1 r2) p =
    intersection (restrictionCurried r1 p) (restrictionCurried r2 p) := by
  simp only [restrictionCurried, intersection, TypedRelation.mk.injEq, true_and]
  grind

-- Theorem: curried version of `restriction_comm`
theorem restrictionCurried_comm (p1 p2 : curriedPred (cols := colType))
    (r : TypedRelation colType) :
    restrictionCurried (restrictionCurried r p2) p1 =
    restrictionCurried (restrictionCurried r p1) p2 := by
  simp_all only [restrictionCurried]
  ext x
  · grind
  · grind

-- Theorem: curried version of `restriction_idempotence`
theorem restrictionCurried_idempotence (p : curriedPred (cols := colType))
    (r : TypedRelation colType) :
    restrictionCurried (restrictionCurried r p) p = restrictionCurried r p := by
  simp only [restrictionCurried, TypedRelation.mk.injEq, Finset.filter_eq_self, Finset.mem_filter,
    and_imp, imp_self, implies_true, and_self]

-- Theorem: curried version of `restriction_cascade`
@[grind =]
theorem restrictionCurried_cascade (p1 p2 : curriedPred (cols := colType))
    (r : TypedRelation colType) :
    restrictionCurried (restrictionCurried r p2) p1 =
    restrictionCurried r (andCurried p1 p2) := by
  simp only [restrictionCurried, TypedRelation.mk.injEq, true_and]
  ext x
  simp [applyCurried_andCurried]
  grind

-- Theorem: curried version of `restriction_diff_distrib`
theorem restrictionCurried_diff_distrib (p : curriedPred (cols := colType))
    (r1 r2 : TypedRelation colType) :
    restrictionCurried (minus r1 r2) p =
    minus (restrictionCurried r1 p) (restrictionCurried r2 p) := by
  simp only [restrictionCurried, minus]
  ext x
  · grind
  · grind

-- Theorem: curried version of `restriction_diff_conj_restriction`
@[grind =]
theorem restrictionCurried_diff_conj_restriction (p q : curriedPred (cols := colType))
    (r : TypedRelation colType) :
    minus (restrictionCurried r p) (restrictionCurried r q) =
    restrictionCurried r (andCurried p (notCurried q)) := by
  simp_all only [minus, restrictionCurried, TypedRelation.mk.injEq, true_and]
  ext x
  simp [applyCurried_andCurried, applyCurried_notCurried]
  grind

-- Theorem: curried version of `restriction_empty`
theorem restrictionCurried_empty (p : curriedPred (cols := colType)) (l : Fin n → String) :
    (restrictionCurried (emptyRel l) p).rows = ∅ := by
  simp only [restrictionCurried, emptyRel]
  grind

-- Theorem: curried version of `restriction_monotone`
theorem restrictionCurried_monotone (p : curriedPred (cols := colType))
    (r1 r2 : TypedRelation colType) :
    r1.rows ⊆ r2.rows →
    (restrictionCurried r1 p).rows ⊆ (restrictionCurried r2 p).rows := by
  intro h x hx
  simp only [restrictionCurried, Finset.mem_filter] at hx ⊢
  exact ⟨h hx.1, hx.2⟩

-- Theorem: curried version of `restriction_push_inter_left`
theorem restrictionCurried_push_inter_left (p : curriedPred (cols := colType))
    (r1 r2 : TypedRelation colType) :
    restrictionCurried (intersection r1 r2) p =
    intersection (restrictionCurried r1 p) r2 := by
  simp only [restrictionCurried, intersection]
  ext x
  · grind
  · grind

end LeanDatabase
