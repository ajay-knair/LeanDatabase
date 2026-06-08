import Mathlib

/-!
# Bag-semantics aggregation, grouping and left-join

The relational algebra in `LeanDatabase.RelationalAlgebra` uses **set semantics**
(`Finset` of dependently-typed tuples). That is the right model for σ/∪/∩/−, but it is a
poor fit for the operations real query optimizers spend most of their time on:

* **aggregation** (`COUNT`, `SUM`) needs to fold over a *bag* — duplicates matter and the
  empty aggregate has a designated zero;
* **`GROUP BY`** partitions rows by a key and aggregates each group;
* **`LEFT JOIN`** probes one relation for a key and yields `NULL` (here `Option.none`) on a
  miss, which `COALESCE` then replaces with a default.

-/

namespace LeanDatabase.Aggregation

variable {Row : Type} {Key : Type} {A : Type} [DecidableEq Key]

/-! ## Selection and aggregation primitives -/

/-- `SELECT * FROM rows WHERE key(r) = k`: the correlated subgroup for `k`.
    (This is exactly what a correlated subquery `WHERE o.cid = c.cid` scans.) -/
def group (key : Row → Key) (k : Key) (rows : List Row) : List Row :=
  rows.filter (fun r => decide (key r = k))

/-- `COUNT(*)` over a bag (duplicates included, empty ↦ 0). -/
def bagCount (rows : List Row) : Nat := rows.length

/-- `COALESCE(SUM(f), 0)` over a bag (empty ↦ 0). -/
def bagSum (f : Row → Int) (rows : List Row) : Int := (rows.map f).sum

/-- The distinct group keys present, i.e. `SELECT DISTINCT key FROM rows`. -/
def keys (key : Row → Key) (rows : List Row) : List Key := (rows.map key).dedup

/-! ## GROUP BY and LEFT JOIN -/

/-- `SELECT key, agg(group) FROM rows GROUP BY key`.

    `agg k g` builds one aggregate row from the key `k` and its group `g`; it must tag the
    output row with its key, recovered by `akey` (see `lookup_groupBy`'s `hkey`). One output
    row per distinct key. -/
def groupBy (key : Row → Key) (agg : Key → List Row → A) (rows : List Row) : List A :=
  (keys key rows).map (fun k => agg k (group key k rows))

/-- The probe side of a `LEFT JOIN ... ON akey(a) = k`: the matching aggregate row, or
    `none` (a NULL row) when the key has no group. -/
def lookup? (akey : A → Key) (k : Key) (aggs : List A) : Option A :=
  aggs.find? (fun a => decide (akey a = k))

/-! ## Basic theorems

These are the building blocks: how membership of keys, emptiness of groups and the simple
aggregates interact. They are the lemmas you reach for when proving equivalences. -/

@[simp] theorem bagCount_nil : bagCount ([] : List Row) = 0 := rfl

@[simp] theorem bagSum_nil (f : Row → Int) : bagSum f [] = 0 := rfl

/-- `COUNT` over a concatenation adds (e.g. `COUNT` distributes over `UNION ALL`). -/
@[simp] theorem bagCount_append (xs ys : List Row) :
    bagCount (xs ++ ys) = bagCount xs + bagCount ys := by
  simp [bagCount]

/-- `SUM` over a concatenation adds (e.g. `SUM` distributes over `UNION ALL`). -/
@[simp] theorem bagSum_append (f : Row → Int) (xs ys : List Row) :
    bagSum f (xs ++ ys) = bagSum f xs + bagSum f ys := by
  simp [bagSum]

/-- `CASE WHEN cond THEN f ELSE 0` as a function. Named (not an inline lambda) so the
    rewrite below keeps a first-order, `grind`-matchable left-hand side. -/
def caseSum (cond : Row → Bool) (f : Row → Int) : Row → Int := fun r => bif cond r then f r else 0

/-- `SUM(CASE WHEN cond THEN f ELSE 0)` over all rows equals `SUM(f)` over the rows passing
    `cond`. This is exactly why a `WHERE` filter can replace a `CASE` inside an aggregate (the
    HAVING / SUM-CASE rewrite): the zeroed-out rows contribute nothing. -/
@[grind =] theorem bagSum_caseSum_eq_filter (cond : Row → Bool) (f : Row → Int) (g : List Row) :
    bagSum (caseSum cond f) g = bagSum f (g.filter cond) := by
  induction g with
  | nil => simp [bagSum]
  | cons r g ih =>
    simp only [bagSum] at ih ⊢
    cases h : cond r <;>
      simp [caseSum, h, List.map_cons, List.sum_cons, ih]

/-- A key is a group key iff some row carries it. -/
theorem mem_keys_iff (key : Row → Key) (k : Key) (rows : List Row) :
    k ∈ keys key rows ↔ ∃ r ∈ rows, key r = k := by
  simp [keys, List.mem_dedup, List.mem_map]

/-- The group of an absent key is empty (the `LEFT JOIN` "miss" case). -/
theorem group_eq_nil_of_not_mem (key : Row → Key) (k : Key) (rows : List Row)
    (h : k ∉ keys key rows) : group key k rows = [] := by
  rw [mem_keys_iff] at h
  simp only [not_exists, not_and] at h
  rw [group, List.filter_eq_nil_iff]
  intro r hr
  simp only [decide_eq_true_eq]
  exact h r hr

/-- Conversely, a present key has a non-empty group. -/
theorem group_ne_nil_of_mem (key : Row → Key) (k : Key) (rows : List Row)
    (h : k ∈ keys key rows) : group key k rows ≠ [] := by
  rw [mem_keys_iff] at h
  obtain ⟨r, hr, hk⟩ := h
  have : r ∈ group key k rows := by simp [group, List.mem_filter, hr, hk]
  exact List.ne_nil_of_mem this

/-- Every row belongs to its own group. -/
@[grind .]
theorem self_mem_group (key : Row → Key) (r : Row) (rows : List Row)
    (h : r ∈ rows) : r ∈ group key (key r) rows := by
  simp [group, List.mem_filter, h]

/-- A key has a (non-empty) group iff it is a group key. This is the bridge between the
    `EXISTS (correlated subquery)` view and the `key IN (SELECT key ...)` view: both ask
    "does this key occur in the other table?". -/
theorem mem_keys_iff_group_ne_nil (key : Row → Key) (k : Key) (rows : List Row) :
    k ∈ keys key rows ↔ group key k rows ≠ [] := by
  constructor
  · exact group_ne_nil_of_mem key k rows
  · intro h
    by_contra hk
    exact h (group_eq_nil_of_not_mem key k rows hk)

/-! ## The grouping engine

`lookup_groupBy` is the key lemma: probing a `GROUP BY` result for a key returns exactly the
aggregate of that key's correlated subgroup, or `none` when the key is absent. Everything
about "GROUP BY then LEFT JOIN" reduces to this. -/

/-- Helper: `find?` over a list of aggregates built from a key list. -/
theorem find?_map_agg (key : Row → Key) (akey : A → Key)
    (agg : Key → List Row → A) (hkey : ∀ k g, akey (agg k g) = k)
    (rows : List Row) (k : Key) (ks : List Key) :
    (ks.map (fun k' => agg k' (group key k' rows))).find? (fun a => decide (akey a = k))
      = if k ∈ ks then some (agg k (group key k rows)) else none := by
  induction ks with
  | nil => simp
  | cons k' ks ih =>
    have hk' : akey (agg k' (group key k' rows)) = k' := hkey _ _
    simp only [List.map_cons, List.find?_cons]
    by_cases hkk : k' = k
    · subst hkk
      simp [hk']
    · have hfalse : decide (akey (agg k' (group key k' rows)) = k) = false := by
        simp [hk', hkk]
      rw [hfalse, ih]
      grind only [= List.mem_cons]

/-- **Grouping engine.** Looking up key `k` in a `GROUP BY` result equals aggregating `k`'s
    correlated subgroup directly — or `none` when `k` is absent.

    `hkey` says the aggregate tags each output row with its own group key (true of any honest
    `GROUP BY key`). This is the workhorse for the correlated-subquery rewrite. -/
@[grind .]
theorem lookup_groupBy (key : Row → Key) (akey : A → Key)
    (agg : Key → List Row → A) (hkey : ∀ k g, akey (agg k g) = k)
    (k : Key) (rows : List Row) :
    lookup? akey k (groupBy key agg rows)
      = if k ∈ keys key rows then some (agg k (group key k rows)) else none := by
  unfold lookup? groupBy
  exact find?_map_agg key akey agg hkey rows k (keys key rows)

/-- Grouping a `WHERE`-filtered table = filtering each group: `group` commutes with `filter`.
    (Lets us relate `GROUP BY` over a filtered relation to `GROUP BY` over the whole one.) -/
@[grind =] theorem group_filter (key : Row → Key) (k : Key) (p : Row → Bool) (rows : List Row) :
    group key k (rows.filter p) = (group key k rows).filter p := by
  simp only [group, List.filter_filter]
  congr 1
  funext r
  exact Bool.and_comm _ _

/-- Membership in a `GROUP BY` result: a row is present iff its key is a group key and it is
    exactly that key's aggregate. (`hkey`: the aggregate tags each row with its own key.) -/
theorem mem_groupBy (key : Row → Key) (akey : A → Key) (agg : Key → List Row → A)
    (hkey : ∀ k g, akey (agg k g) = k) (rows : List Row) (a : A) :
    a ∈ groupBy key agg rows ↔
      akey a ∈ keys key rows ∧ a = agg (akey a) (group key (akey a) rows) := by
  unfold groupBy
  rw [List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [hkey]
    exact ⟨hk, rfl⟩
  · rintro ⟨hk, ha⟩
    exact ⟨akey a, hk, ha.symm⟩

/-- A `GROUP BY` result has no duplicate rows (one row per distinct key). -/
@[simp]
theorem groupBy_nodup (key : Row → Key) (akey : A → Key) (agg : Key → List Row → A)
    (hkey : ∀ k g, akey (agg k g) = k) (rows : List Row) :
    (groupBy key agg rows).Nodup := by
  unfold groupBy
  apply (List.nodup_dedup _).map
  intro k1 k2 h
  have := congrArg akey h
  rwa [hkey, hkey] at this

/-! ## Group maximum ("latest / greatest row per group")

`MAX(f)` over a group, and the fact that "`f r` equals the group max" is the same as "`r` is
`f`-maximal in its group". This is the content of the *greatest-N-per-group* rewrite
(`MAX` self-join ≡ `NOT EXISTS` a-strictly-greater row). -/

/-- Every member of a `Nat` list is `≤` its `foldr max 0`. -/
@[grind .]
theorem le_foldr_max (a : Nat) (L : List Nat) (h : a ∈ L) :
    a ≤ L.foldr max 0 := by
  induction L with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact (ih h).trans (Nat.le_max_right _ _)

/-- A `foldr max 0` is `≤` any bound that dominates every element. -/
@[grind .]
theorem foldr_max_le (b : Nat) (L : List Nat) (h : ∀ a ∈ L, a ≤ b) :
    L.foldr max 0 ≤ b := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons, Nat.max_le]
    exact ⟨h x (List.mem_cons_self ..), ih fun a ha => h a (List.mem_cons_of_mem _ ha)⟩

/-- `MAX(f)` over the group of key `k`, as a `Nat` (empty group ↦ 0). -/
@[grind =]
def groupMaxBy (key : Row → Key) (f : Row → Nat) (k : Key) (rows : List Row) : Nat :=
  ((group key k rows).map f).foldr max 0

/-- Every row in a group has `f`-value `≤` the group `MAX(f)`. -/
@[grind .] theorem le_groupMaxBy (key : Row → Key) (f : Row → Nat) (k : Key) (rows : List Row)
    (r : Row) (h : r ∈ group key k rows) : f r ≤ groupMaxBy key f k rows :=
  le_foldr_max (f r) _ (List.mem_map_of_mem h)

/-- `f r` is the group `MAX(f)` **iff** `r` is `f`-maximal in its group. The right-hand side is
    the `NOT EXISTS (a strictly greater row)` condition; the left-hand side is the `MAX`
    self-join condition. -/
@[grind .] theorem eq_groupMaxBy_iff (key : Row → Key) (f : Row → Nat) (k : Key)
    (rows : List Row) (r : Row) (hr : r ∈ group key k rows) :
    f r = groupMaxBy key f k rows ↔ ∀ r2 ∈ group key k rows, f r2 ≤ f r := by
  constructor
  · intro h r2 hr2
    rw [h]; exact le_groupMaxBy key f k rows r2 hr2
  · intro h
    exact Nat.le_antisymm (le_groupMaxBy key f k rows r hr)
      (foldr_max_le (f r) _ (by simpa using fun r2 hr2 => h r2 hr2))

/-! ## `grind` configuration

We register the lemmas above (and the two relevant `List` congruence lemmas) with `grind`
 -/
attribute [grind =] lookup_groupBy group_eq_nil_of_not_mem bagCount bagSum
  bagCount_append bagSum_append
attribute [grind →] group_ne_nil_of_mem
attribute [grind .] List.map_congr_left List.filter_congr

end LeanDatabase.Aggregation
