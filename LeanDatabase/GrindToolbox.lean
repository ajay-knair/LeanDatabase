import LeanDatabase.RelationalAlgebra
import LeanDatabase.Aggregation

/-!
# Grind toolbox — a big bag of database-flavoured rewrite lemmas

Importing this module registers a large pile of small, "obviously true" database identities
with `grind`, so that downstream query-equivalence theorems close with a bare `grind +locals`.
Two flavours:

* **bag/`List` track** (this namespace): grouping, aggregation and filtering identities;
* **set/`TypedRelation` track** (re-tagging existing `RelationalAlgebra` lemmas at the bottom).

Everything tagged `@[grind =]` is an *oriented, terminating* rewrite (no commutativity /
associativity — those would loop). Symmetric facts are deliberately left untagged.
-/

namespace LeanDatabase.Aggregation

variable {Row : Type} {Key : Type} {A : Type} [DecidableEq Key]

/-! ## Grouping identities -/

/-- Grouping an empty table gives an empty group. -/
@[grind =] theorem group_nil (key : Row → Key) (k : Key) :
    group key k ([] : List Row) = [] := rfl

/-- Grouping distributes over `UNION ALL` (list append). -/
@[grind =] theorem group_append (key : Row → Key) (k : Key) (xs ys : List Row) :
    group key k (xs ++ ys) = group key k xs ++ group key k ys := by
  simp [group, List.filter_append]

/-- Membership in a group: in the table, and carrying the group key. -/
@[grind =] theorem mem_group (key : Row → Key) (k : Key) (rows : List Row) (r : Row) :
    r ∈ group key k rows ↔ r ∈ rows ∧ key r = k := by
  simp [group, List.mem_filter]

/-- Grouping by the same key twice is idempotent. -/
@[grind =] theorem group_group (key : Row → Key) (k : Key) (rows : List Row) :
    group key k (group key k rows) = group key k rows := by
  simp [group, List.filter_filter]

/-! ## Distinct keys -/

/-- No keys in an empty table. -/
@[grind =] theorem keys_nil (key : Row → Key) : keys key ([] : List Row) = [] := rfl

/-- The list of keys has no duplicates. -/
theorem keys_nodup (key : Row → Key) (rows : List Row) :
    (keys key rows).Nodup := List.nodup_dedup _

/-! ## Aggregates: `COUNT` and `SUM` -/

/-- `COUNT` of a one-row bag. -/
@[grind =] theorem bagCount_singleton (r : Row) : bagCount [r] = 1 := rfl

/-- `SUM` of a one-row bag. -/
@[grind =] theorem bagSum_singleton (f : Row → Int) (r : Row) : bagSum f [r] = f r := by
  simp [bagSum]

/-- `COUNT` is the bag length. -/
@[grind =] theorem bagCount_eq_length (rows : List Row) : bagCount rows = rows.length := rfl

/-- Splitting a `COUNT` by a predicate and its negation (a complete partition). -/
@[grind =] theorem bagCount_filter_add_not (p : Row → Bool) (rows : List Row) :
    bagCount (rows.filter p) + bagCount (rows.filter (fun r => !p r)) = bagCount rows := by
  induction rows with
  | nil => simp [bagCount]
  | cons r rs ih =>
    cases h : p r <;> simp [bagCount, h] at * <;> omega

/-- Splitting a `SUM` by a predicate and its negation (a complete partition). -/
@[grind =] theorem bagSum_filter_add_not (f : Row → Int) (p : Row → Bool) (rows : List Row) :
    bagSum f (rows.filter p) + bagSum f (rows.filter (fun r => !p r)) = bagSum f rows := by
  induction rows with
  | nil => simp [bagSum]
  | cons r rs ih =>
    cases h : p r <;>
      simp only [bagSum] at ih ⊢ <;>
      simp [h, List.map_cons, List.sum_cons] <;> omega

/-! ## `GROUP BY` membership (akey-free) and `Perm`

`mem_groupBy'` characterises membership of a `GROUP BY` result without the recovery function
`akey`, so it is usable as a `grind` rewrite. `perm_of_nodup_mem` lets a multiset (`Perm`)
equivalence be reduced to "same membership" once both sides are duplicate-free. -/

/-- A row is in `GROUP BY key agg rows` iff it is the aggregate of some present key. -/
@[grind =] theorem mem_groupBy' (key : Row → Key) (agg : Key → List Row → A)
    (rows : List Row) (a : A) :
    a ∈ groupBy key agg rows ↔ ∃ k ∈ keys key rows, agg k (group key k rows) = a := by
  simp [groupBy, List.mem_map]

/-- Two duplicate-free lists with the same members are permutations (same multiset). -/
theorem perm_of_nodup_mem (l1 l2 : List A) (h1 : l1.Nodup) (h2 : l2.Nodup)
    (h : ∀ a, a ∈ l1 ↔ a ∈ l2) : l1.Perm l2 :=
  (List.perm_ext_iff_of_nodup h1 h2).mpr h

end LeanDatabase.Aggregation

/-! ## Set / `TypedRelation` track

Re-tag a curated set of existing relational-algebra identities as oriented `grind` rewrites.
-/

namespace LeanDatabase

attribute [grind =]
  restriction_idempotence          -- σ_p(σ_p R) = σ_p R
  inter_idempotence                -- R ∩ R = R
  union_absorb_inter               -- R ∪ (R ∩ S) = R
  inter_absorb_union               -- R ∩ (R ∪ S) = R
  diff_empty                       -- R − ∅ = R
  union_identity                   -- R ∪ ∅ = R
  restriction_inter_distrib        -- σ_p(R ∩ S) = σ_p R ∩ σ_p S
  restriction_diff_distrib         -- σ_p(R − S) = σ_p R − σ_p S

end LeanDatabase
