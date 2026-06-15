import LeanDatabase.Operators.CrossProduct

/-!
# Joins

Every join in one place, layered on the cross-product machinery in `CrossProduct`:

* **`join`** (θ-join) — `crossProductRel` filtered by a condition.
* **`semijoin`/`antijoin`** (`⋉`/`▷`) — *schema-preserving*; they keep the left columns only and
  model `WHERE EXISTS`/`IN` and `WHERE NOT EXISTS`/`NOT IN`.
* **`leftOuterJoin`/`rightOuterJoin`/`fullOuterJoin`** (`⟕`/`⟖`/`⟗`) — inner-join matches `∪` the
  unmatched rows of the outer side(s) padded with `NULL`s. These need the **nullable** layer
  (`fun i => Option (colType i)`), so the `NULL` primitives (`liftNullable`, `nullRow`) and the
  three-valued column helpers (`isNull`/`isNotNull`/`coalesce`) live here too.
-/

namespace LeanDatabase

variable {n m : Nat}
variable {colType1 : Fin n → Type} [∀ i, DecidableEq (colType1 i)]
variable {colType2 : Fin m → Type} [∀ i, DecidableEq (colType2 i)]

/-
## Join Operation
This join operation is simply filtering of cross product for given condition
-/

@[simp, grind .]
def join (r1 : TypedRelation colType1) (r2 : TypedRelation colType2) (table1_alias: String := "L") (table2_alias: String := "R")
    (condition : TypedTuple (Fin.append colType1 colType2) → Bool) :
    TypedRelation (Fin.append colType1 colType2) :=

  let product := crossProductRel r1 r2 table1_alias table2_alias
  {
    labels := product.labels,
    rows   := product.rows.filter (fun t => condition t)
  }

-- Theorem: Join Empty Left
-- ∅ ⋈ R = ∅
theorem join_empty_left (r1 : TypedRelation colType1) (r2 : TypedRelation colType2)
    (condition : TypedTuple (Fin.append colType1 colType2) → Bool) (a1 a2 : String)
    (h : r1.rows = ∅) :
    (join r1 r2 a1 a2 condition).rows = ∅ := by
  grind

-- Theorem: Join Empty Right
-- R ⋈ ∅ = ∅
theorem join_empty_right (r1 : TypedRelation colType1) (r2 : TypedRelation colType2)
    (condition : TypedTuple (Fin.append colType1 colType2) → Bool) (a1 a2 : String)
    (h : r2.rows = ∅) :
    (join r1 r2 a1 a2 condition).rows = ∅ := by
  grind

-- Theorem: Join Size Upper Bound
-- |R ⋈ S| <= |R| * |S|
-- "A join can never create more rows than the cross product."
theorem join_card_bound (r1 : TypedRelation colType1) (r2 : TypedRelation colType2)
    (condition : TypedTuple (Fin.append colType1 colType2) → Bool) (a1 a2 : String) :
    (join r1 r2 a1 a2 condition).rows.card ≤ r1.rows.card * r2.rows.card := by
  simp only [join]
  have h_filter : (Finset.filter (fun t => condition t) (crossProductRel r1 r2 a1 a2).rows).card
                  ≤ (crossProductRel r1 r2 a1 a2).rows.card := by
    apply Finset.card_filter_le
  rw [crossProduct_card] at h_filter
  exact h_filter

-- Theorem: Filter Merge
-- σ_p ( R ⋈ _c S ) = R ⋈ _{c && p} S
-- "Filtering a join result is the same as adding the filter to the join condition."
-- (This is useful: The database can check 'p' while joining, instead of doing a second pass)
theorem join_filter_merge (r1 : TypedRelation colType1) (r2 : TypedRelation colType2)
    (c : TypedTuple (Fin.append colType1 colType2) → Bool) -- Join Condition
    (p : TypedTuple (Fin.append colType1 colType2) → Bool) -- Filter Condition
    (a1 a2 : String) :

    (join r1 r2 a1 a2 c).rows.filter (fun t => p t) =
    (join r1 r2 a1 a2 (fun t => c t && p t)).rows := by
  grind

-- Theorem: Join is Subset of Cross Product
-- (R ⋈ S) ⊆ (R x S)
theorem join_subset_crossProduct (r1 : TypedRelation colType1) (r2 : TypedRelation colType2)
    (condition : TypedTuple (Fin.append colType1 colType2) → Bool) (a1 a2 : String) :
    (join r1 r2 a1 a2 condition).rows ⊆ (crossProductRel r1 r2 a1 a2).rows := by
  grind

-- Theorem: Join Commutativity (up to the schema half-swap)
-- (R ⋈_c S)  ≅  (S ⋈_{c∘swap} R)
-- "Swapping the join operands gives the same rows once you swap the two schema halves
--  (`swapAppend`) and transport the condition through that swap."  The two sides have *different*
--  dependent schemas (`Fin.append c1 c2` vs `Fin.append c2 c1`), so equality is stated on `.rows`
--  modulo `swapAppend`.
theorem join_comm (r1 : TypedRelation colType1) (r2 : TypedRelation colType2)
    (cond : TypedTuple (Fin.append colType1 colType2) → Bool) (a1 a2 : String) :
    (join r1 r2 a1 a2 cond).rows.image swapAppend
      = (join r2 r1 a2 a1 (fun u => cond (swapAppend u))).rows := by
  ext u
  simp only [join, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨t, ⟨htmem, htcond⟩, rfl⟩
    rw [mem_crossProduct] at htmem
    rw [mem_crossProduct, splitTuple_swapAppend, swapAppend_swapAppend]
    exact ⟨⟨htmem.2, htmem.1⟩, htcond⟩
  · rintro ⟨humem, hucond⟩
    rw [mem_crossProduct] at humem
    refine ⟨swapAppend u, ⟨?_, hucond⟩, swapAppend_swapAppend u⟩
    rw [mem_crossProduct, splitTuple_swapAppend]; exact ⟨humem.2, humem.1⟩

-- Theorem: Join condition congruence — pointwise-equal conditions give the same join.
-- (Closes `ON a=b` vs `ON b=a` once the two conditions are shown equal, e.g. by `eq_comm`.)
theorem join_cond_congr (r1 : TypedRelation colType1) (r2 : TypedRelation colType2) (a1 a2 : String)
    (c c' : TypedTuple (Fin.append colType1 colType2) → Bool) (h : ∀ t, c t = c' t) :
    join r1 r2 a1 a2 c = join r1 r2 a1 a2 c' := by
  have : c = c' := funext h; rw [this]

-- Theorem: first-order **join-order swap under a projection**. Projecting a join and projecting the
-- operand-swapped join (with condition + projection transported through `swapAppend`) give the same
-- rows — a directly usable corollary of `join_comm` for "same query, operands swapped, then SELECT".
theorem join_comm_image {γ : Type} [DecidableEq γ]
    (r1 : TypedRelation colType1) (r2 : TypedRelation colType2) (a1 a2 : String)
    (cond : TypedTuple (Fin.append colType1 colType2) → Bool)
    (proj : TypedTuple (Fin.append colType1 colType2) → γ) :
    (join r1 r2 a1 a2 cond).rows.image proj
      = (join r2 r1 a2 a1 (fun u => cond (swapAppend u))).rows.image (fun u => proj (swapAppend u)) := by
  rw [← join_comm r1 r2 cond a1 a2, Finset.image_image]
  apply Finset.image_congr
  intro t _
  simp only [Function.comp_apply, swapAppend_swapAppend]

-- Theorem: **selection pushdown into the left join input** — a `WHERE` reading only the left
-- columns can be applied to the left table before joining: `σ_{pL∘left}(R ⋈ S) = (σ_{pL} R) ⋈ S`.
theorem restriction_join_left (r1 : TypedRelation colType1) (r2 : TypedRelation colType2)
    (a1 a2 : String) (cond : TypedTuple (Fin.append colType1 colType2) → Bool)
    (pL : TypedTuple colType1 → Bool) :
    restriction (fun t => pL (splitTuple t).1) (join r1 r2 a1 a2 cond)
      = join (restriction pL r1) r2 a1 a2 cond := by
  apply TypedRelation.ext
  · rfl
  · ext t
    simp only [restriction, join, Finset.mem_filter, mem_crossProduct]
    grind

/-
## Semi-join and Anti-join
Unlike the (cross-product based) `join`, these are SCHEMA-PRESERVING: the output keeps the left
relation's columns, so they need no `Fin.append` and no `NULL`s. They model `WHERE EXISTS`/`IN`
(semi-join `R ⋉ S`) and `WHERE NOT EXISTS`/`NOT IN` (anti-join `R ▷ S`).
-/

-- `R ⋉ S`: rows of `R` having at least one `S` row satisfying `cond`.
@[simp, grind]
def semijoin (r1 : TypedRelation colType1) (r2 : TypedRelation colType2)
    (cond : TypedTuple colType1 → TypedTuple colType2 → Bool) : TypedRelation colType1 :=
  restriction (fun t => decide (∃ s ∈ r2.rows, cond t s)) r1

-- `R ▷ S`: rows of `R` with NO `S` row satisfying `cond`.
@[simp, grind]
def antijoin (r1 : TypedRelation colType1) (r2 : TypedRelation colType2)
    (cond : TypedTuple colType1 → TypedTuple colType2 → Bool) : TypedRelation colType1 :=
  restriction (fun t => decide (¬ ∃ s ∈ r2.rows, cond t s)) r1

-- Theorem: a semi-join keeps a subset of the left relation.
theorem semijoin_subset (r1 : TypedRelation colType1) (r2 : TypedRelation colType2)
    (cond : TypedTuple colType1 → TypedTuple colType2 → Bool) :
    (semijoin r1 r2 cond).rows ⊆ r1.rows := by
  simp only [semijoin, restriction]
  exact Finset.filter_subset _ _

-- Theorem: the anti-join is exactly the rows the semi-join drops: `R ▷ S = R − (R ⋉ S)`.
theorem antijoin_eq_minus_semijoin (r1 : TypedRelation colType1) (r2 : TypedRelation colType2)
    (cond : TypedTuple colType1 → TypedTuple colType2 → Bool) :
    antijoin r1 r2 cond = minus r1 (semijoin r1 r2 cond) := by
  simp only [antijoin, semijoin, minus, restriction, TypedRelation.mk.injEq, true_and]
  ext t
  simp only [Finset.mem_filter, Finset.mem_sdiff, decide_eq_true_eq, decide_not,
    Bool.not_eq_true', decide_eq_false_iff_not]
  grind

-- Theorem: semi-join and anti-join partition the left relation.
theorem semijoin_union_antijoin (r1 : TypedRelation colType1) (r2 : TypedRelation colType2)
    (cond : TypedTuple colType1 → TypedTuple colType2 → Bool) :
    (semijoin r1 r2 cond).rows ∪ (antijoin r1 r2 cond).rows = r1.rows := by
  simp only [semijoin, antijoin, restriction]
  ext t
  simp only [Finset.mem_union, Finset.mem_filter, decide_eq_true_eq, decide_not,
    Bool.not_eq_true', decide_eq_false_iff_not]
  grind

/-
## NULL handling and outer joins

The base `TypedRelation colType` has no `NULL`s — every column `i` carries a real `colType i`.
We model `NULL` the standard way: a **nullable** column family `fun i => Option (colType i)`, with
`NULL = none`. The outer joins are *inner-join matches* `∪` *the unmatched rows padded with
`NULL`s* (the unmatched side is exactly the anti-join). The padded side uses
`crossProductRel … (nullRow …)`, so the combined output schema is produced by the same
`Fin.append` machinery as the inner join — no new tuple plumbing.
-/

/-! ### Three-valued column helpers (`IS NULL` / `IS NOT NULL` / `COALESCE`) -/

/-- `col IS NULL`. -/
@[simp, grind] def isNull {l : Nat} {colType : Fin l → Type} {α : Type}
    (proj : TypedTuple colType → Option α) : TypedTuple colType → Bool := fun t => (proj t).isNone

/-- `col IS NOT NULL`. -/
@[simp, grind] def isNotNull {l : Nat} {colType : Fin l → Type} {α : Type}
    (proj : TypedTuple colType → Option α) : TypedTuple colType → Bool := fun t => (proj t).isSome

/-- `COALESCE(col, default)` — replace `NULL` by `default`. -/
@[simp, grind] def coalesce {l : Nat} {colType : Fin l → Type} {α : Type}
    (proj : TypedTuple colType → Option α) (dflt : α) : TypedTuple colType → α :=
  fun t => (proj t).getD dflt

/-! ### Nullable primitives -/

/-- Lift a `NOT NULL` relation into the nullable schema: every value `v` becomes `some v`. -/
@[simp] def liftNullable {l : Nat} {ct : Fin l → Type} [∀ i, DecidableEq (ct i)]
    (r : TypedRelation ct) : TypedRelation (fun i => Option (ct i)) :=
  { labels := r.labels, rows := r.rows.image (fun t i => some (t i)) }

/-- A single all-`NULL` row over the nullable version of `ct` (the right pad of a `LEFT JOIN`). -/
@[simp] def nullRow {l : Nat} (ct : Fin l → Type) [∀ i, DecidableEq (ct i)] (lbl : Fin l → String) :
    TypedRelation (fun i => Option (ct i)) :=
  { labels := lbl, rows := {fun (_ : Fin l) => none} }

/-! ### Outer joins -/

section OuterJoins
variable [∀ i, Inhabited (colType1 i)] [∀ i, Inhabited (colType2 i)]

/-- `R ⟕ S` (`LEFT OUTER JOIN`): inner-join matches, plus every unmatched `R` row padded with
`NULL`s on the `S` columns. Output schema `R ++ Option S`. -/
@[simp] def leftOuterJoin (r1 : TypedRelation colType1) (r2 : TypedRelation colType2)
    (cond : TypedTuple colType1 → TypedTuple colType2 → Bool)
    (a1 : String := "L") (a2 : String := "R") :
    TypedRelation (Fin.append colType1 (fun i => Option (colType2 i))) :=
  union
    (join r1 (liftNullable r2) a1 a2
      (fun t => cond (splitTuple t).1 (fun i => ((splitTuple t).2 i).get!)))
    (crossProductRel (antijoin r1 r2 cond) (nullRow colType2 r2.labels) a1 a2)

/-- `R ⟖ S` (`RIGHT OUTER JOIN`): the mirror image — unmatched `S` rows padded with `NULL`s on the
`R` columns. Output schema `Option R ++ S`. -/
@[simp] def rightOuterJoin (r1 : TypedRelation colType1) (r2 : TypedRelation colType2)
    (cond : TypedTuple colType1 → TypedTuple colType2 → Bool)
    (a1 : String := "L") (a2 : String := "R") :
    TypedRelation (Fin.append (fun i => Option (colType1 i)) colType2) :=
  union
    (join (liftNullable r1) r2 a1 a2
      (fun t => cond (fun i => ((splitTuple t).1 i).get!) (splitTuple t).2))
    (crossProductRel (nullRow colType1 r1.labels) (antijoin r2 r1 (fun s t => cond t s)) a1 a2)

/-- `R ⟗ S` (`FULL OUTER JOIN`): matches with both sides present, plus the unmatched rows of each
side padded with `NULL`s on the other. Output schema `Option R ++ Option S`. -/
@[simp] def fullOuterJoin (r1 : TypedRelation colType1) (r2 : TypedRelation colType2)
    (cond : TypedTuple colType1 → TypedTuple colType2 → Bool)
    (a1 : String := "L") (a2 : String := "R") :
    TypedRelation (Fin.append (fun i => Option (colType1 i)) (fun i => Option (colType2 i))) :=
  union
    (union
      (join (liftNullable r1) (liftNullable r2) a1 a2
        (fun t => cond (fun i => ((splitTuple t).1 i).get!) (fun i => ((splitTuple t).2 i).get!)))
      (crossProductRel (liftNullable (antijoin r1 r2 cond)) (nullRow colType2 r2.labels) a1 a2))
    (crossProductRel (nullRow colType1 r1.labels)
      (liftNullable (antijoin r2 r1 (fun s t => cond t s))) a1 a2)

end OuterJoins

/-- Lifting to the nullable schema preserves cardinality (`some` is injective). -/
@[grind =] theorem liftNullable_card {l : Nat} {ct : Fin l → Type} [∀ i, DecidableEq (ct i)]
    (r : TypedRelation ct) : (liftNullable r).rows.card = r.rows.card := by
  simp only [liftNullable]
  refine Finset.card_image_of_injective _ ?_
  intro a b h
  funext i
  have := congrFun h i
  simpa using this

/-- A freshly lifted (`NOT NULL`) relation has **no** `NULL`s: `WHERE col IS NULL` is empty. -/
theorem liftNullable_isNull_empty {l : Nat} {ct : Fin l → Type} [∀ i, DecidableEq (ct i)]
    (r : TypedRelation ct) (i : Fin l) :
    (restriction (isNull (fun t => t i)) (liftNullable r)).rows = ∅ := by
  simp only [restriction, liftNullable, isNull]
  rw [Finset.filter_eq_empty_iff]
  intro t ht
  simp only [Finset.mem_image] at ht
  obtain ⟨s, _, rfl⟩ := ht
  simp

end LeanDatabase
