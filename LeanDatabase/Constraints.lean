import LeanDatabase.Operators.Aggregate

/-!
# Data constraints (hypotheses) — turning data-dependent equivalences into provable ones

Apart from just the column names and their types, they also have hypothesis and relations amongst each other.
To support proving equivalences that depend on such data facts, we would need to encode them and provide to the proof system.

-/

namespace LeanDatabase

variable {n : Nat} {colType : Fin n → Type} [∀ i, DecidableEq (colType i)]

/-- **Functional dependency** `key → det` over `R`: any two rows of `R` agreeing on `key` agree on
`det`. -/
def FuncDepEq {α β : Type} (key : TypedTuple colType → α) (det : TypedTuple colType → β)
    (R : TypedRelation colType) : Prop :=
  ∀ a ∈ R.rows, ∀ b ∈ R.rows, key a = key b → det a = det b

/-- **Same-partition ⇒ same group count.** If two group keys cut `R` into the same per-row classes
(`key1 s = key1 t ↔ key2 s = key2 t` for every row `s`), the group of `t` has the same `COUNT(*)`
under either key. The bridge from a functional dependency to a `GROUP BY`-granularity rewrite. -/
theorem cnt_eq_of_partition_eq {α β : Type} [DecidableEq α] [DecidableEq β]
    (key1 : TypedTuple colType → α) (key2 : TypedTuple colType → β)
    (R : TypedRelation colType) (t : TypedTuple colType)
    (h : ∀ s ∈ R.rows, (key1 s = key1 t) ↔ (key2 s = key2 t)) :
    TypedAgg.cnt key1 (key1 t) R = TypedAgg.cnt key2 (key2 t) R := by
  have hrows : (TypedAgg.grp key1 (key1 t) R).rows = (TypedAgg.grp key2 (key2 t) R).rows := by
    unfold TypedAgg.grp restriction
    grind only [Finset.filter_congr]
  grind [TypedAgg.cnt]

/-- **`GROUP BY key` ≡ `GROUP BY (det, key)`** counts, given the FD `key → det`. The refined key
`(det, key)` and the coarse key `key` induce the same partition, so every group's `COUNT(*)` agrees
(hence any `ORDER BY COUNT(*)`/top-N over the groups agrees). `det` is listed first to match SQL
`GROUP BY id, name` written as `(id, name)`. -/
theorem cnt_pair_eq_of_FD {α β : Type} [DecidableEq α] [DecidableEq β]
    (key : TypedTuple colType → α) (det : TypedTuple colType → β)
    (R : TypedRelation colType) (hfd : FuncDepEq key det R)
    (t : TypedTuple colType) (ht : t ∈ R.rows) :
    TypedAgg.cnt key (key t) R = TypedAgg.cnt (fun s => (det s, key s)) (det t, key t) R := by
  apply cnt_eq_of_partition_eq
  grind only [FuncDepEq]

/-- **`GROUP BY (det, key)` collapses to `GROUP BY key`** under the FD `key → det`. This is the
*terminating* (`@[simp]`) orientation of `cnt_pair_eq_of_FD`: it rewrites the **finer** grouping to
the **coarser** one, so it can't re-match its own result. With the FD in context, `sql_simp` closes a
`GROUP BY id, name ≡ GROUP BY name` count equality by itself. -/
@[simp] theorem cnt_collapse_of_FD {α β : Type} [DecidableEq α] [DecidableEq β]
    (key : TypedTuple colType → α) (det : TypedTuple colType → β)
    (R : TypedRelation colType) (hfd : FuncDepEq key det R)
    (t : TypedTuple colType) (ht : t ∈ R.rows) :
    TypedAgg.cnt (fun s => (det s, key s)) (det t, key t) R = TypedAgg.cnt key (key t) R := by
  apply cnt_eq_of_partition_eq
  grind only [FuncDepEq]

/-- **`COUNT(DISTINCT g) = COUNT(DISTINCT f)`** when `g` factors through `f` on `R` via an injective
`φ` (i.e. `g = φ ∘ f` on the rows and `φ` is injective on the `f`-values). This is the honest data
fact behind `COUNT(DISTINCT name)` ≡ `COUNT(DISTINCT code)` (a name↔code bijection) and
`COUNT(DISTINCT key) = COUNT(*)`-style rewrites. -/
theorem relCountDistinct_eq_of_factor {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : TypedTuple colType → α) (g : TypedTuple colType → β) (R : TypedRelation colType) (φ : α → β)
    (hφ : ∀ a ∈ R.rows, g a = φ (f a))
    (hinj : Set.InjOn φ ↑(R.rows.image f)) :
    TypedAgg.relCountDistinct g R = TypedAgg.relCountDistinct f R := by
  have key : R.rows.image g = (R.rows.image f).image φ := by
    grind only [= Finset.mem_image]
  grind [Finset.card_image_of_injOn hinj]

/-- **Same-kernel ⇒ same distinct count** (fiber form, `φ`-free). If `f` and `g` induce the same
partition on `s` (`f a = f b ↔ g a = g b` for all rows), they have equally many distinct values.
Stated at the `card (image …)` level — the shape `relCountDistinct` unfolds to — and tagged `@[grind]`
so `sql_equiv` closes `COUNT(DISTINCT a) = COUNT(DISTINCT b)` from the bijection hypothesis alone. -/
theorem card_image_eq_of_fiber {α γ δ : Type} [DecidableEq γ] [DecidableEq δ]
    (s : Finset α) (f : α → γ) (g : α → δ)
    (h : ∀ a ∈ s, ∀ b ∈ s, f a = f b ↔ g a = g b) :
    (s.image f).card = (s.image g).card := by
  classical
  apply Finset.card_bij (fun v hv => g (Finset.mem_image.mp hv).choose)
  repeat grind [Finset.mem_image_of_mem]

end LeanDatabase
