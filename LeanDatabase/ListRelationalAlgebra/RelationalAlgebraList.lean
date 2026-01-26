import Mathlib
import LeanDatabase.ListRelationalAlgebra.TypedListRelation

namespace LeanDatabase

namespace ListRelation

/-
# Relational Algebra

We prove some of the basic properties of Relational Algebra on our existing definition.
-/

variable {n : Nat} {types : Fin n → Type}
variable [∀ i, DecidableEq (types i)]

/-! ### Commutativity & Associativity -/

-- Theorem: Union is Commutative ( R ∪ S = S ∪ R )
theorem union_comm (r1 r2 : TypedListRelation types) (h : r1.labels = r2.labels) :
    union r1 r2 ~ union r2 r1 := by
  simp_all only [equivalent, union, true_and]
  grind

-- Theorem: Union is Associative
-- (R ⋃ S) ⋃ T = R ⋃ (S ⋃ T)
omit [(i : Fin n) → DecidableEq (types i)] in
theorem union_assoc (r1 r2 r3 : TypedListRelation types) :
    union (union r1 r2) r3 ~ union r1 (union r2 r3) := by
  simp_all only [union, equivalent]
  simp only [List.append_assoc, List.Perm.refl, and_self]

-- Theorem: Intersection is Commutative ( R ∩ S = S ∩ R)
theorem inter_comm (r1 r2 : TypedListRelation types) (h : r1.labels = r2.labels) :
    intersection r1 r2 ~ intersection r2 r1 := by
  simp_all only [equivalent, intersection, List.contains_eq_mem, true_and]
  sorry
-- Theorem: Idempotence of Intersection
-- R ∩ R = R
theorem inter_idempotence (r : TypedListRelation types) :
    intersection r r ~ r := by
  simp_all only [equivalent, intersection, List.contains_eq_mem, true_and]
  sorry

-- Theorem: Absorption Law
-- R ∪ (R ∩ S) = R
theorem union_absorb_inter (r1 r2 : TypedListRelation types) :
    union r1 (intersection r1 r2) ~ r1 := by
  simp_all only [equivalent, intersection, List.contains_eq_mem]
  sorry

-- Theorem: Distributivity of Intersection over Union
-- R ∩ (S ∪ T) = (R ∩ S) ∪ (R ∩ T)
-- "Joining a combined table is the same as joining each part separately."
theorem inter_distrib_union (r1 r2 r3 : TypedListRelation types) :
    intersection r1 (union r2 r3) ~ union (intersection r1 r2) (intersection r1 r3) := by
  simp only [intersection, union, TypedListRelation.mk.injEq, true_and]
  sorry

-- Theorem: Distributivity of Union over Intersection
-- R ∪ (S ∩ T) = (R ∪ S) ∩ (R ∪ T)
theorem union_distrib_inter (r1 r2 r3 : TypedListRelation types) :
    union r1 (intersection r2 r3) ~ intersection (union r1 r2) (union r1 r3) := by
  simp_all only [equivalent, intersection]
  sorry

-- Theorem: Dual Absorption Law
-- R ∩ (R ∪ S) = R
theorem inter_absorb_union (r1 r2 : TypedListRelation types) :
    intersection r1 (union r1 r2) ~ r1 := by
  simp_all only [equivalent, intersection, true_and]
  sorry

-- Theorem: Difference Chain
-- (R - S) - T = R - (S ∪ T)
-- "Excluding S then excluding T is the same as excluding (S or T) at once."
theorem diff_diff_eq_diff_union (r s t : TypedListRelation types) :
    minus (minus r s) t ~ minus r (union s t) := by
  simp_all [minus, union]

-- Theorem: Identity for Difference
-- R - ∅ = R
theorem diff_empty (r : TypedListRelation types) :
    minus r (emptyListRel r.labels) ~ r := by
  simp_all [emptyListRel]

-- Theorem: Zero for Difference (Left)
-- ∅ - R = ∅
theorem empty_diff (r : TypedListRelation types) :
    (minus (emptyListRel r.labels) r).rows ~ [] := by
  simp only [minus, emptyListRel, Finset.empty_sdiff]

-- Theorem: Self-Difference is Empty
-- R - R = ∅
theorem diff_self (r : TypedListRelation types) :
    (minus r r).rows ~ [] := by
    simp only [minus, sdiff_self, Finset.bot_eq_empty]

/-! ### Distributivity-/

-- Theorem: Selection Distributes over Union
-- σ_p(R ∪ S) = σ_p(R) ∪ σ_p(S)
theorem restriction_union_distrib (p : TypedTuple types → Bool)
    (r1 r2 : TypedListRelation types) :
    restriction p (union r1 r2) ~ union (restriction p r1) (restriction p r2) := by
  simp only [restriction, union, TypedListRelation.mk.injEq, true_and]
  grind

-- Theorem: Selection Distributes over Intersection
-- σ_p(R ∩ S) = σ_p(R) ∩ σ_p(S)
theorem restriction_inter_distrib (p : TypedTuple types → Bool)
    (r1 r2 : TypedListRelation types) :
    restriction p (intersection r1 r2) ~ intersection (restriction p r1) (restriction p r2) := by
  simp_all [restriction, intersection, TypedListRelation.mk.injEq, true_and]
  sorry

/-! ### Selection Properties (Filtering Logic) -/

-- Theorem: Commutativity of Selection
-- σ_a( σ_b( R ) ) = σ_b( σ_a( R ) )
-- "The order of filters does not matter"
omit [∀ i, DecidableEq (types i)] in
theorem restriction_comm (p1 p2 : (TypedTuple types → Bool)) (r : TypedListRelation types) :
    restriction p1 (restriction p2 r) ~ restriction p2 (restriction p1 r) := by
  simp_all only [restriction]
  sorry


-- Theorem: Idempotence of Selection
-- σ_p ( σ_p ( R ) ) = σ_p( R )
-- "Filtering twice is the same as filtering once"
omit [∀ i, DecidableEq (types i)] in
theorem restriction_idempotence (p : TypedTuple types → Bool) (r : TypedListRelation types) :
    restriction p (restriction p r) ~ restriction p r := by
  simp only [restriction, TypedListRelation.mk.injEq, Finset.filter_eq_self, Finset.mem_filter, and_imp,
    imp_self, implies_true, and_self]
  sorry


/-! ### Cascading Selection (Splitting Logic) -/

-- Theorem: Cascading Selection
-- σ_{p1}(σ_{p2}(R)) = σ_{p1 ∧ p2}(R)
-- "Applying two filters sequentially is the same as applying them combined with AND."
omit [∀ i, DecidableEq (types i)] in
theorem restriction_cascade (p1 p2 : (TypedTuple types → Bool)) (r : TypedListRelation types) :
    restriction p1 (restriction p2 r) ~
    restriction (fun x => p1 x && p2 x) r := by
  simp only [restriction, Bool.and_eq_true, TypedListRelation.mk.injEq, true_and]
  sorry

/-! ### Difference Properties -/

-- Theorem: Selection Distributes over Difference
-- σ_p(R - S) = σ_p(R) - σ_p(S)
-- "You can filter the rows before calculating the difference."
theorem restriction_diff_distrib (p : TypedTuple types → Bool) (r1 r2 : TypedListRelation types) :
    restriction p (minus r1 r2) ~ minus (restriction p r1) (restriction p r2) := by
  simp only [restriction, minus]
  sorry

-- Theorem: Difference of Restrictions
-- σ_P(R) - σ_Q(R) = σ_{P ∧ ¬Q}(R)
-- "Subtracting a filtered set from another filtered set (of the same source)
theorem restriction_diff_conj_restriction (p q : TypedTuple types → Bool) (r : TypedListRelation types) :
    minus (restriction p r) (restriction q r) ~ restriction (fun t => p t && !q t) r := by
  simp_all only [minus, restriction, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    TypedListRelation.mk.injEq, true_and]
  sorry

/-! ### Identity and Zero Laws -/

-- Theorem: Selection on Empty is Empty
-- σ(∅) = ∅
omit [∀ i, DecidableEq (types i)] in
theorem restriction_empty (p :  TypedTuple types → Bool) (l : Fin n → String) :
    (restriction p (emptyListRel l)).rows ~ [] := by
  simp only [restriction, emptyListRel]
  sorry

-- Theorem: Identity for Union
-- R ∪ ∅ = R
omit [(i : Fin n) → DecidableEq (types i)] in
theorem union_identity (r : TypedListRelation types) :
    union r (emptyListRel r.labels) ~ r := by
  simp only [union, emptyListRel]
  simp_all

-- Theorem: Zero for Intersection
-- R ∩ ∅ = ∅
theorem inter_zero (r : TypedListRelation types) :
    (intersection r (emptyListRel r.labels)).rows ~ ∅ := by
  exact Finset.disjoint_iff_inter_eq_empty.mp fun ⦃x⦄ a a_1 ↦ a_1

/-! ### Monotonicity -/

-- Theorem: Selection is Monotone
-- If R ⊆ S, then σ(R) ⊆ σ(S)
omit [∀ i, DecidableEq (types i)] in
theorem restriction_monotone (p : (TypedTuple types → Bool)) (r1 r2 : TypedListRelation types) :
    r1.rows ⊆ r2.rows →
    (restriction p r1).rows ⊆ (restriction p r2).rows := by
  sorry

/-! ### Other Important Theorems -/
-- Theorem: Push Selection into Intersection (Left Side)
-- σ_p(R ∩ S) = σ_p(R) ∩ S
-- "If you join two tables and then filter, it is slow. You can filter first and then join."
theorem restriction_push_inter_left (p : TypedTuple types → Bool) (r1 r2 : TypedListRelation types) :
    restriction p (intersection r1 r2) ~ intersection (restriction p r1) r2 := by
  simp only [restriction, intersection]
  sorry

-- Theorem: De Morgan's Law for Difference
-- R - (S ∪ T) = (R - S) ∩ (R - T)
theorem diff_union_distrib (r s t : TypedListRelation types) :
    minus r (union s t) ~ intersection (minus r s) (minus r t) := by
  simp only [minus, union, intersection]
  sorry

end ListRelation
end LeanDatabase
