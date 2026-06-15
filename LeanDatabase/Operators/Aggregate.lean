import LeanDatabase.RelationalAlgebra

/-!
# Aggregation over `TypedRelation` (set semantics)

Aggregation (`COUNT`, `SUM`, `MIN`, `MAX`, `AVG`, `GROUP BY`, correlated subqueries) built
**directly on the `TypedRelation` relational algebra** — rows are `TypedTuple`s, tables are
`TypedRelation`s (`Finset` of tuples), grouping reuses the defined `restriction`. Set semantics:
input tables are assumed duplicate-free, under which `COUNT`/`SUM` over distinct rows agree with
SQL.

Two layers: **grouped** scalars (`grp`/`cnt`/`sumI`/`okeys`/`groupMaxN`, take a key) and
**ungrouped** whole-relation aggregates (`relCount`/`relSum`/`relMax`/`relMin`/`relCountDistinct`/
`relAvg`); compose the latter with `grp key k rel` for `GROUP BY`.
-/

namespace LeanDatabase.TypedAgg

open LeanDatabase

variable {n : Nat} {colType : Fin n → Type} [∀ i, DecidableEq (colType i)]
variable {K : Type} [DecidableEq K]

/-! ## Grouping + grouped aggregates -/

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
    `SUM(f)` over its `WHERE p` `restriction`: rows failing `p` contribute `0` either way. -/
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

/-- **`COUNT` coalesce.** `LEFT JOIN`+`COALESCE(_,0)` count equals the correlated count. -/
@[simp] theorem coalesce_cnt (key : TypedTuple colType → K) (k : K) (rel : TypedRelation colType) :
    (if k ∈ okeys key rel then cnt key k rel else 0) = cnt key k rel := by
  split
  · rfl
  · rename_i h; exact (cnt_eq_zero_of_not_mem key k rel h).symm

/-- **`SUM` coalesce.** `LEFT JOIN`+`COALESCE(_,0)` sum equals the correlated sum. -/
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

/-- `f t` is the group `MAX(f)` **iff** `t` is `f`-maximal in its group. -/
@[grind .] theorem eq_groupMaxN_iff (key : TypedTuple colType → K) (k : K)
    (rel : TypedRelation colType) (f : TypedTuple colType → Nat) (t : TypedTuple colType)
    (ht : t ∈ (grp key k rel).rows) :
    f t = groupMaxN key k rel f ↔ ∀ s ∈ (grp key k rel).rows, f s ≤ f t := by
  unfold groupMaxN
  constructor
  · intro h s hs; rw [h]; exact Finset.le_sup hs
  · intro h
    exact Nat.le_antisymm (Finset.le_sup ht) (Finset.sup_le h)

/-- `simp`-friendly form of `eq_groupMaxN_iff` keyed on table membership `t ∈ rel.rows`. -/
@[simp] theorem eq_groupMaxN_table (key : TypedTuple colType → K) (f : TypedTuple colType → Nat)
    (rel : TypedRelation colType) (t : TypedTuple colType) (ht : t ∈ rel.rows) :
    (f t = groupMaxN key (key t) rel f) ↔ ∀ s ∈ (grp key (key t) rel).rows, f s ≤ f t :=
  eq_groupMaxN_iff key (key t) rel f t (self_mem_grp key rel t ht)

/-- A group is non-empty iff its key occurs (`EXISTS`/`IN`/`NOT EXISTS`/`NOT IN` bridge). -/
@[grind =] theorem grp_nonempty_iff (key : TypedTuple colType → K) (k : K)
    (rel : TypedRelation colType) : (grp key k rel).rows.Nonempty ↔ k ∈ okeys key rel := by
  simp only [grp, restriction, okeys, Finset.Nonempty, Finset.mem_filter, Finset.mem_image,
    decide_eq_true_eq]

/-- A group is empty iff its key is absent (the `=∅` normal form of `grp_nonempty_iff`, so the
    anti-join rewrites close regardless of which form `sql_simp` leaves). -/
@[simp, grind =] theorem grp_empty_iff (key : TypedTuple colType → K) (k : K)
    (rel : TypedRelation colType) : (grp key k rel).rows = ∅ ↔ k ∉ okeys key rel := by
  rw [← Finset.not_nonempty_iff_eq_empty, grp_nonempty_iff]

/-! ## Ungrouped (whole-relation) aggregates

For `GROUP BY` apply these to `grp key k rel`. `MAX`/`MIN` are NULL-aware (`WithBot`/`WithTop`,
`⊥`/`⊤` for the empty relation, matching SQL `MAX`/`MIN` of no rows = `NULL`); `AVG` returns
`(SUM, COUNT)` so the caller owns the division and the empty-relation `NULL`. -/

/-- `COUNT(*)`. -/
@[simp, grind] def relCount (rel : TypedRelation colType) : Nat := rel.rows.card

/-- `SUM(f)`. -/
@[simp, grind] def relSum (f : TypedTuple colType → Int) (rel : TypedRelation colType) : Int :=
  ∑ t ∈ rel.rows, f t

/-- `MAX(f)` (`⊥`/`NULL` on the empty relation). -/
@[simp, grind] def relMax (f : TypedTuple colType → Nat) (rel : TypedRelation colType) : WithBot Nat :=
  (rel.rows.image f).max

/-- `MIN(f)` (`⊤`/`NULL` on the empty relation). -/
@[simp, grind] def relMin (f : TypedTuple colType → Nat) (rel : TypedRelation colType) : WithTop Nat :=
  (rel.rows.image f).min

/-- `COUNT(DISTINCT f)`. -/
@[simp, grind] def relCountDistinct {β : Type} [DecidableEq β]
    (f : TypedTuple colType → β) (rel : TypedRelation colType) : Nat :=
  (rel.rows.image f).card

/-- `AVG(f)` as `(SUM, COUNT)`. -/
@[simp, grind] def relAvg (f : TypedTuple colType → Int) (rel : TypedRelation colType) : Int × Nat :=
  (relSum f rel, relCount rel)

/-- `COUNT(*)` after a `WHERE` never exceeds the original count. -/
theorem relCount_restriction_le (p : TypedTuple colType → Bool) (rel : TypedRelation colType) :
    relCount (restriction p rel) ≤ relCount rel := by
  simp only [relCount, restriction]; exact Finset.card_filter_le _ _

/-- `COUNT(DISTINCT f) ≤ COUNT(*)`. -/
theorem relCountDistinct_le {β : Type} [DecidableEq β]
    (f : TypedTuple colType → β) (rel : TypedRelation colType) :
    relCountDistinct f rel ≤ relCount rel := by
  simp only [relCountDistinct, relCount]; exact Finset.card_image_le

/-- **`COUNT(*) = COUNT(DISTINCT key)` when `key` is a key** (injective on the rows). The honest
fact behind `COUNT(DISTINCT pk) = COUNT(*)`. -/
theorem relCount_eq_relCountDistinct_of_injOn {β : Type} [DecidableEq β]
    (key : TypedTuple colType → β) (rel : TypedRelation colType)
    (hinj : Set.InjOn key ↑rel.rows) :
    relCount rel = relCountDistinct key rel := by
  simp only [relCount, relCountDistinct, (Finset.card_image_of_injOn hinj)]

/-- **`MAX` over a union** is the `sup` of the two `MAX`es (`WithBot`). -/
@[grind =] theorem relMax_union (f : TypedTuple colType → Nat) (r s : TypedRelation colType) :
    relMax f (union r s) = relMax f r ⊔ relMax f s := by
  simp only [relMax, union, Finset.image_union, Finset.max_union]

/-- **`MIN` over a union** is the `inf` of the two `MIN`s (`WithTop`). -/
@[grind =] theorem relMin_union (f : TypedTuple colType → Nat) (r s : TypedRelation colType) :
    relMin f (union r s) = relMin f r ⊓ relMin f s := by
  simp only [relMin, union, Finset.image_union, Finset.min_union]

/-! ## Additivity over a disjoint union, and the GROUP BY total -/

/-- `COUNT(*)` is additive over a disjoint union (`UNION ALL` of disjoint relations). -/
@[grind =] theorem relCount_union_disjoint (r s : TypedRelation colType)
    (h : Disjoint r.rows s.rows) :
    relCount (union r s) = relCount r + relCount s := by
  simp only [relCount, union]
  exact Finset.card_union_of_disjoint h

/-- `SUM(f)` is additive over a disjoint union. -/
@[grind =] theorem relSum_union_disjoint (f : TypedTuple colType → Int)
    (r s : TypedRelation colType) (h : Disjoint r.rows s.rows) :
    relSum f (union r s) = relSum f r + relSum f s := by
  simp only [relSum, union]
  exact Finset.sum_union h

/-- **The GROUP BY total**: summing each group's `COUNT(*)` over all present keys gives the table's
    total `COUNT(*)`. (`∑_{k} cnt(k) = COUNT(*)`, the fiberwise partition by `key`.) -/
@[grind =] theorem sum_cnt_okeys_eq_relCount (key : TypedTuple colType → K)
    (rel : TypedRelation colType) :
    (∑ k ∈ okeys key rel, cnt key k rel) = relCount rel := by
  simp only [cnt, grp, restriction, okeys, relCount, decide_eq_true_eq]
  rw [Finset.card_eq_sum_card_fiberwise (fun t ht => Finset.mem_image_of_mem key ht)]

/-! ## Aggregates of the empty relation (`GROUP BY` over no rows) -/

/-- `COUNT(*)` of an empty relation is `0`. -/
@[simp, grind =] theorem relCount_empty (l : Fin n → String) :
    relCount (emptyRel (colType := colType) l) = 0 := by
  simp [relCount, emptyRel]

/-- `SUM(f)` of an empty relation is `0`. -/
@[simp, grind =] theorem relSum_empty (f : TypedTuple colType → Int) (l : Fin n → String) :
    relSum f (emptyRel (colType := colType) l) = 0 := by
  simp [relSum, emptyRel]

/-- `MAX(f)` of an empty relation is `⊥` (SQL `NULL`). -/
@[simp, grind =] theorem relMax_empty (f : TypedTuple colType → Nat) (l : Fin n → String) :
    relMax f (emptyRel (colType := colType) l) = ⊥ := by
  simp [relMax, emptyRel]

/-- `MIN(f)` of an empty relation is `⊤` (SQL `NULL`). -/
@[simp, grind =] theorem relMin_empty (f : TypedTuple colType → Nat) (l : Fin n → String) :
    relMin f (emptyRel (colType := colType) l) = ⊤ := by
  simp [relMin, emptyRel]

/-! ## `grind` configuration -/
attribute [grind .] Finset.image_congr Finset.filter_congr Finset.sum_union

end LeanDatabase.TypedAgg

/- Re-export the aggregate operators into the top-level `LeanDatabase` namespace-/
namespace LeanDatabase
export LeanDatabase.TypedAgg
  (grp cnt sumI okeys groupMaxN relCount relSum relMax relMin relCountDistinct relAvg)
end LeanDatabase
