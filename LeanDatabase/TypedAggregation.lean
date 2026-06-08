import LeanDatabase.RelationalAlgebra

/-!
# Typed aggregation over `TypedRelation` (set semantics)

Aggregation (`COUNT`, `SUM`, `GROUP BY`, correlated subqueries) built **directly on the
`TypedRelation` relational algebra** of `LeanDatabase.TypedRelation` — rows are `TypedTuple`s,
tables are `TypedRelation`s (`Finset` of tuples), and grouping reuses the defined `restriction`
operator. Per the project convention everything uses that algebra.

We work under **set semantics** (the `Finset` model deduplicates). The standing assumption is
that input tables are duplicate-free, under which `COUNT`/`SUM` over distinct rows agree with
SQL and the rewrites are sound. (`UNION ALL`-style multiplicity is the one thing this model
cannot see — see `Examples/Example6`.)
-/

namespace LeanDatabase.TypedAgg

open LeanDatabase

variable {n : Nat} {colType : Fin n → Type} [∀ i, DecidableEq (colType i)]
variable {K : Type} [DecidableEq K]

/-- `SELECT * FROM rel WHERE key(t) = k` — a group, as a `restriction` of the relation. -/
def grp (key : TypedTuple colType → K) (k : K) (rel : TypedRelation colType) :
    TypedRelation colType :=
  restriction (fun t => decide (key t = k)) rel

/-- `COUNT(*)` over the group of key `k`. -/
def cnt (key : TypedTuple colType → K) (k : K) (rel : TypedRelation colType) : Nat :=
  (grp key k rel).rows.card

/-- `SUM(f)` over the group of key `k`. -/
def sumI (key : TypedTuple colType → K) (k : K) (rel : TypedRelation colType)
    (f : TypedTuple colType → Int) : Int :=
  ∑ t ∈ (grp key k rel).rows, f t

/-- `SELECT DISTINCT key FROM rel` — the group keys present. -/
def okeys (key : TypedTuple colType → K) (rel : TypedRelation colType) : Finset K :=
  rel.rows.image key

/-- A key occurs iff some row carries it. -/
@[grind =] theorem mem_okeys (key : TypedTuple colType → K) (k : K) (rel : TypedRelation colType) :
    k ∈ okeys key rel ↔ ∃ t ∈ rel.rows, key t = k := by
  simp [okeys, Finset.mem_image]

/-- The group of an absent key is empty (the `LEFT JOIN` miss). -/
theorem grp_empty_of_not_mem (key : TypedTuple colType → K) (k : K) (rel : TypedRelation colType)
    (h : k ∉ okeys key rel) : (grp key k rel).rows = ∅ := by
  rw [mem_okeys] at h
  simp only [not_exists, not_and] at h
  simp only [grp, restriction, Finset.filter_eq_empty_iff, decide_eq_true_eq]
  exact fun t ht hk => h t ht hk

/-- `COUNT` of an absent key's group is `0`. -/
@[grind =] theorem cnt_eq_zero_of_not_mem (key : TypedTuple colType → K) (k : K)
    (rel : TypedRelation colType) (h : k ∉ okeys key rel) : cnt key k rel = 0 := by
  simp [cnt, grp_empty_of_not_mem key k rel h]

/-- `SUM` of an absent key's group is `0`. -/
@[grind =] theorem sum_eq_zero_of_not_mem (key : TypedTuple colType → K) (k : K)
    (rel : TypedRelation colType) (f : TypedTuple colType → Int) (h : k ∉ okeys key rel) :
    sumI key k rel f = 0 := by
  simp [sumI, grp_empty_of_not_mem key k rel h]

/-- **`CASE` → `WHERE` pushdown.** `SUM(CASE WHEN p THEN f ELSE 0)` over a relation equals
    `SUM(f)` over its `WHERE p` `restriction`: the rows failing `p` contribute `0` either way.
    The general identity behind the HAVING/`SUM(CASE)` rewrite (see `Examples/Example12`). -/
@[grind .]
theorem sum_case_eq_sum_where (p : TypedTuple colType → Bool) (f : TypedTuple colType → Int)
    (rel : TypedRelation colType) :
    (∑ t ∈ rel.rows, (if p t then f t else 0)) = ∑ t ∈ (restriction p rel).rows, f t := by
  simp only [restriction]
  rw [Finset.sum_filter]

/-- The `COUNT` analogue: `SUM(CASE WHEN p THEN 1 ELSE 0)` = `COUNT(*)` over the `WHERE p` rows. -/
@[grind .]
theorem sum_indicator_eq_count_where (p : TypedTuple colType → Bool)
    (rel : TypedRelation colType) :
    (∑ t ∈ rel.rows, (if p t then (1 : Nat) else 0)) = (restriction p rel).rows.card := by
  simp only [restriction, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- **`COUNT` coalesce.** The `LEFT JOIN`+`COALESCE(_,0)` count equals the correlated count:
    on a join miss the group is empty (count `0`), exactly the `COALESCE` default. -/
@[simp] theorem coalesce_cnt (key : TypedTuple colType → K) (k : K) (rel : TypedRelation colType) :
    (if k ∈ okeys key rel then cnt key k rel else 0) = cnt key k rel := by
  split
  · rfl
  · rename_i h; exact (cnt_eq_zero_of_not_mem key k rel h).symm

/-- **`SUM` coalesce.** The `LEFT JOIN`+`COALESCE(_,0)` sum equals the correlated sum. -/
@[simp] theorem coalesce_sum (key : TypedTuple colType → K) (k : K) (rel : TypedRelation colType)
    (f : TypedTuple colType → Int) :
    (if k ∈ okeys key rel then sumI key k rel f else 0) = sumI key k rel f := by
  split
  · rfl
  · rename_i h; exact (sum_eq_zero_of_not_mem key k rel f h).symm

/-- Every row belongs to its own group. -/
@[grind .] theorem self_mem_grp (key : TypedTuple colType → K) (rel : TypedRelation colType)
    (t : TypedTuple colType) (h : t ∈ rel.rows) : t ∈ (grp key (key t) rel).rows := by
  simp [grp, restriction, Finset.mem_filter, h]

/-- `MAX(f)` over the group of key `k` (a `Nat` column), as a `Finset.sup` (empty ↦ 0). -/
def groupMaxN (key : TypedTuple colType → K) (k : K) (rel : TypedRelation colType)
    (f : TypedTuple colType → Nat) : Nat :=
  (grp key k rel).rows.sup f

/-- `f t` is the group `MAX(f)` **iff** `t` is `f`-maximal in its group — the `MAX` self-join
    condition equals the `NOT EXISTS (a strictly greater row)` condition. -/
@[grind .] theorem eq_groupMaxN_iff (key : TypedTuple colType → K) (k : K)
    (rel : TypedRelation colType) (f : TypedTuple colType → Nat) (t : TypedTuple colType)
    (ht : t ∈ (grp key k rel).rows) :
    f t = groupMaxN key k rel f ↔ ∀ s ∈ (grp key k rel).rows, f s ≤ f t := by
  unfold groupMaxN
  constructor
  · intro h s hs; rw [h]; exact Finset.le_sup hs
  · intro h
    exact Nat.le_antisymm (Finset.le_sup ht) (Finset.sup_le h)

/-- A group is non-empty iff its key occurs (bridge for `EXISTS`/`IN`/`NOT EXISTS`/`NOT IN`). -/
@[grind =] theorem grp_nonempty_iff (key : TypedTuple colType → K) (k : K)
    (rel : TypedRelation colType) : (grp key k rel).rows.Nonempty ↔ k ∈ okeys key rel := by
  simp only [grp, restriction, okeys, Finset.Nonempty, Finset.mem_filter, Finset.mem_image,
    decide_eq_true_eq]

/-! ## `grind` configuration

Register the `Finset` congruence lemmas (so a whole-table `image`/`filter` equality reduces to
the per-row goal) and the membership bridge, so the migrated aggregation examples close with a
bare `grind +locals`. The coalesce lemmas above are `@[simp]` (their `ite` head can't be a
`grind` rewrite pattern) and are picked up by `grind`'s simp normalisation. -/
attribute [grind .] Finset.image_congr Finset.filter_congr Finset.sum_union

end LeanDatabase.TypedAgg
