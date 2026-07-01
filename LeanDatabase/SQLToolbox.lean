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

open LeanDatabase.TypedAgg

variable {n : Nat} {colType : Fin n → Type} [∀ i, DecidableEq (colType i)]

/-- **`HAVING SUM(...) ≠ 0` ⟹ the key survived**: a non-zero group `SUM` witnesses that the group is
non-empty, i.e. the key occurs among the aggregated table's keys. The `HAVING` counterpart of
`groupSum_eq_zero_of_not_mem`; lets `sql_equiv` recover "this key passed a `HAVING SUM(...) > c ≥ 0`
test, so it is present after the `WHERE`-restricted `GROUP BY`". -/
@[grind →] theorem mem_groupKeys_of_groupSum_ne_zero {K : Type} [DecidableEq K]
    (key : TypedTuple colType → K) (k : K) (rel : TypedRelation colType)
    (f : TypedTuple colType → Int) (h : groupSum key k rel f ≠ 0) : k ∈ groupKeys key rel := by
  by_contra hk
  exact h (groupSum_eq_zero_of_not_mem key k rel f hk)

/-- The witness form of `mem_groupKeys_of_groupSum_ne_zero`: a non-zero group `SUM` produces an
actual row of the group. Handed to `grind` directly so it can discharge "`HAVING SUM(...) ≠ 0` ⟹ ∃
such a row" without having to compose `mem_groupKeys_of_groupSum_ne_zero` with `mem_groupKeys`. -/
@[grind →] theorem exists_mem_of_groupSum_ne_zero {K : Type} [DecidableEq K]
    (key : TypedTuple colType → K) (k : K) (rel : TypedRelation colType)
    (f : TypedTuple colType → Int) (h : groupSum key k rel f ≠ 0) :
    ∃ t ∈ rel.rows, key t = k := by
  rw [← mem_groupKeys]
  exact mem_groupKeys_of_groupSum_ne_zero key k rel f h

/-- **`groupKeys` is monotone under `WHERE`**: a key present after a `restriction` is present in the
whole relation. The other half of matching two `GROUP BY`s whose bases differ by a `WHERE`. -/
@[grind →] theorem mem_groupKeys_of_mem_restriction {K : Type} [DecidableEq K]
    (key : TypedTuple colType → K) (p : TypedTuple colType → Bool) (rel : TypedRelation colType)
    (k : K) (h : k ∈ groupKeys key (restriction p rel)) : k ∈ groupKeys key rel := by
  simp only [mem_groupKeys, restriction, Finset.mem_filter] at h ⊢
  obtain ⟨t, ⟨ht, _⟩, hk⟩ := h
  exact ⟨t, ht, hk⟩

/-- **`HAVING` absorbs a `WHERE` on the base of a `GROUP BY`.** Two `GROUP BY`s whose per-key output
`mk` and `HAVING` predicate `H` both factor through the group key produce the same table even when
one scans `base` and the other its `WHERE p` `restriction` — provided every `H`-surviving row's key
still occurs after the `WHERE` (`hpres`). This is the whole-relation content of a `SUM(CASE)`+`HAVING`
≡ `WHERE`+`SUM`+`HAVING` rewrite; `hpres` is discharged from `HAVING SUM(...) > c ≥ 0` via
`exists_mem_of_groupSum_ne_zero`. -/
theorem image_where_absorb {K β : Type} [DecidableEq K] [DecidableEq β]
    (key : TypedTuple colType → K) (mk : TypedTuple colType → β) (H : TypedTuple colType → Bool)
    (p : TypedTuple colType → Bool) (base : TypedRelation colType)
    (hH : ∀ s t, key s = key t → H s = H t)
    (hmk : ∀ s t, key s = key t → mk s = mk t)
    (hpres : ∀ t ∈ base.rows, H t = true → key t ∈ groupKeys key (restriction p base)) :
    (restriction H base).rows.image mk = (restriction H (restriction p base)).rows.image mk := by
  apply Finset.ext; intro x
  simp only [Finset.mem_image, restriction, Finset.mem_filter]
  constructor
  · rintro ⟨t, ⟨ht, hHt⟩, rfl⟩
    obtain ⟨s, hs, hks⟩ := (mem_groupKeys _ _ _).mp (hpres t ht hHt)
    simp only [restriction, Finset.mem_filter] at hs
    exact ⟨s, ⟨⟨hs.1, hs.2⟩, (hH s t hks).trans hHt⟩, hmk s t hks⟩
  · rintro ⟨t, ⟨⟨ht, _⟩, hHt⟩, rfl⟩
    exact ⟨t, ⟨ht, hHt⟩, rfl⟩

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
