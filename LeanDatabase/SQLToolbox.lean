import LeanDatabase.RelationalAlgebra
import LeanDatabase.Operators.Aggregate

/-!
# Grind toolbox — database identities registered with `grind`

Importing this module turns a curated, *confluent* set of relational-algebra identities into
oriented `grind` rewrites, so downstream query-equivalence theorems over `TypedRelation` close
with a bare `grind +locals`. (The aggregation lemmas — grouping, `COUNT`/`SUM` coalesce, group
membership/max — are already registered in `LeanDatabase.Operators.Aggregate`, re-exported here.)

Everything tagged `@[grind =]` is an oriented, terminating rewrite — no commutativity /
associativity (those would loop), and no two rules sharing a left-hand side.
-/

namespace LeanDatabase

variable {n : Nat} {colType : Fin n → Type} [∀ i, DecidableEq (colType i)]

/-- The empty relation has no rows. Exposed as a `@[simp]` rewrite (without tagging `emptyRel`
itself, which lives in `TypedRelation`) so `sql_equiv` can collapse `∅`-table queries — e.g.
`LEFT JOIN` against an empty table. -/
@[simp] theorem emptyRel_rows {n : Nat} {colType : Fin n → Type} [∀ i, DecidableEq (colType i)]
    (l : Fin n → String) : (emptyRel (colType := colType) l).rows = ∅ := rfl

/-- **`COUNT` partition** (`Bool` predicate form, matching `restriction`): `COUNT(WHERE p)` plus
    `COUNT(WHERE NOT p)` is `COUNT(*)`. Tagged `@[simp]` so `sql_equiv` closes the partition. -/
@[simp] theorem card_filter_true_add_false {α : Type} [DecidableEq α] (p : α → Bool) (s : Finset α) :
    (s.filter (fun a => p a = true)).card + (s.filter (fun a => p a = false)).card = s.card := by
  simp only [← Bool.not_eq_true]
  exact Finset.card_filter_add_card_filter_not _

/-- **`COUNT` partition by complementary predicates.** A robust generalization of
`card_filter_true_add_false`: it does NOT require the two filters to mention a single shared `p`.
This matters because `simp` De-Morgan-splits a compound `WHERE`/`!WHERE` (e.g. `a ∧ b` vs
`¬a ∨ ¬b`), after which no single `p` survives. Tagged `@[grind]` so `grind` matches the two
`card`s and discharges the `Q ↔ ¬P` side-condition (pure propositional/Boolean reasoning) itself —
closing the partition regardless of how `simp` rewrote the predicates. -/
@[grind =] theorem card_filter_add_card_filter_compl {α : Type} [DecidableEq α] (s : Finset α)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] (h : ∀ a, Q a ↔ ¬ P a) :
    (s.filter P).card + (s.filter Q).card = s.card := by
  have hQ : s.filter Q = s.filter (fun a => ¬ P a) := Finset.filter_congr (fun a _ => h a)
  rw [hQ]
  exact Finset.card_filter_add_card_filter_not _

/-- **`WHERE` congruence**: two `restriction`s are equal when their predicates agree on every row of
the input. The bridge for "the two `WHERE` predicates coincide on the actual data" hypotheses (e.g.
two different `LIKE` patterns that happen to match the same rows of this table). -/
theorem restriction_congr (p q : TypedTuple colType → Bool) (R : TypedRelation colType)
    (h : ∀ t ∈ R.rows, p t = q t) : restriction p R = restriction q R := by
  grind only [= restriction.eq_1, Finset.filter_congr]


attribute [grind =]
  restriction_idempotence          -- σ_p(σ_p R) = σ_p R
  inter_idempotence                -- R ∩ R = R
  union_absorb_inter               -- R ∪ (R ∩ S) = R
  inter_absorb_union               -- R ∩ (R ∪ S) = R
  diff_empty                       -- R − ∅ = R
  union_identity                   -- R ∪ ∅ = R
  restriction_inter_distrib        -- σ_p(R ∩ S) = σ_p R ∩ σ_p S
  restriction_diff_distrib         -- σ_p(R − S) = σ_p R − σ_p S
  projection_compose               -- π_b(π_a R) = π_{a∘b} R          (collapses nested projection)
  inter_distrib_union              -- R ∩ (S ∪ T) = (R∩S) ∪ (R∩T)     (ONLY this direction; union_distrib_inter would loop)
  diff_diff_eq_diff_union          -- (R − S) − T = R − (S ∪ T)       (collapses nested minus)

end LeanDatabase
