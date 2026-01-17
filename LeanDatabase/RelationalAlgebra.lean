import Mathlib
import LeanDatabase.TypedRelation

namespace LeanDatabase

/-
# Relational Algebra

We prove some of the basic properties of Relational Algebra on our existing definition.
-/

variable {n : Nat} {types : Fin n → Type}

/-! ### Commutativity & Associativity -/

-- Theorem: Union is Commutative ( R ∪ S = S ∪ R )
theorem union_comm (r1 r2 : TypedRelation types) (h : r1.labels = r2.labels) :
    union r1 r2 = union r2 r1 := by
  simp_all only [union, TypedRelation.mk.injEq, true_and]
  rw [Set.union_comm] -- Uses Mathlib's proof for Sets

-- Theorem: Union is Associative
theorem union_assoc (r1 r2 r3 : TypedRelation types) :
    union (union r1 r2) r3 = union r1 (union r2 r3) := by
  simp [union]
  rw [Set.union_assoc]

-- Theorem: Intersection is Commutative
theorem inter_comm (r1 r2 : TypedRelation types) (h : r1.labels = r2.labels) :
    intersection r1 r2 = intersection r2 r1 := by
  simp_all only [intersection, TypedRelation.mk.injEq, true_and]
  rw [Set.inter_comm]

/-! ### Distributivity-/

-- Theorem: Selection Distributes over Union
-- σ(R ∪ S) = σ(R) ∪ σ(S)
theorem restriction_union_distrib (p : (i : Fin n) → types i → Bool)
    (r1 r2 : TypedRelation types) :
    restriction p (union r1 r2) = union (restriction p r1) (restriction p r2) := by
  simp only [restriction, union, Set.mem_union, Set.sep_union]

-- Theorem: Selection Distributes over Intersection
-- σ(R ∩ S) = σ(R) ∩ σ(S)
theorem restriction_inter_distrib (p : (i : Fin n) → types i → Bool)
    (r1 r2 : TypedRelation types) :
    restriction p (intersection r1 r2) = intersection (restriction p r1) (restriction p r2) := by
  simp only [restriction, intersection, Set.mem_inter_iff, Set.sep_inter]


/-! ### Selection Properties (Filtering Logic) -/

-- Theorem: Commutativity of Selection
-- σ_a( σ_b( R ) ) = σ_b( σ_a( R ) )
-- "The order of filters does not matter"
theorem restriction_comm (p1 p2 : (i : Fin n) → types i → Bool) (r : TypedRelation types) :
    restriction p1 (restriction p2 r) = restriction p2 (restriction p1 r) := by
  simp_all [restriction]
  grind

-- Theorem: Idempotence of Selection
-- σ_p ( σ_p ( R ) ) = σ_p( R )
-- "Filtering twice is the same as filtering once"
theorem restriction_idempotence (p : (i : Fin n) → types i → Bool) (r : TypedRelation types) :
    restriction p (restriction p r) = restriction p r := by
  simp only [restriction, Set.mem_setOf_eq, and_self_right]


/-! ### Cascading Selection (Splitting Logic) -/

-- Theorem: Cascading Selection
-- σ_{p1}(σ_{p2}(R)) = σ_{p1 ∧ p2}(R)
-- "Applying two filters sequentially is the same as applying them combined with AND."
theorem restriction_cascade (p1 p2 : (i : Fin n) → types i → Bool) (r : TypedRelation types) :
    restriction p1 (restriction p2 r) =
    restriction (fun i x => p1 i x && p2 i x) r := by
  simp [restriction]
  grind

/-! ### Difference Properties -/

-- Theorem: Selection Distributes over Difference
-- σ_p(R - S) = σ_p(R) - σ_p(S)
-- "You can filter the rows before calculating the difference."
theorem restriction_diff_distrib (p : (i : Fin n) → types i → Bool) (r1 r2 : TypedRelation types) :
    restriction p (minus r1 r2) = minus (restriction p r1) (restriction p r2) := by
  simp [restriction, minus]
  ext x
  grind

-- Theorem: Self-Difference is Empty
-- R - R = ∅
theorem diff_self (r : TypedRelation types) :
    (minus r r).rows = ∅ := by
  simp only [minus, sdiff_self, Set.bot_eq_empty]

/-! ### Identity and Zero Laws -/

-- Definition of an Empty Relation (The "Zero" element)
def emptyRel (l : Fin n → String) : TypedRelation types :=
  { labels := l, rows := ∅ }

-- Theorem: Identity for Union
-- R ∪ ∅ = R
theorem union_identity (r : TypedRelation types) :
    union r (emptyRel r.labels) = r := by
  simp only [union, emptyRel, Set.union_empty]

-- Theorem: Zero for Intersection
-- R ∩ ∅ = ∅
theorem inter_zero (r : TypedRelation types) :
    (intersection r (emptyRel r.labels)).rows = ∅ := by
  simp only [intersection, emptyRel, Set.inter_empty]

/-! ### 7. Monotonicity -/

-- Theorem: Selection is Monotone
-- If R ⊆ S, then σ(R) ⊆ σ(S)
theorem restriction_monotone (p : (i : Fin n) → types i → Bool) (r1 r2 : TypedRelation types) :
    r1.rows ⊆ r2.rows →
    (restriction p r1).rows ⊆ (restriction p r2).rows := by
  intro h_subset
  simp [restriction]
  grind

end LeanDatabase
