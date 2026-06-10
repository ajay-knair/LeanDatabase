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
