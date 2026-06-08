import LeanDatabase.TypedAggregation
open LeanDatabase LeanDatabase.TypedAgg

/-!
# Example 6 — Partitioned aggregation ≡ summing per-shard partials

Aggregating one combined table equals aggregating each partition and adding the partials —
the correctness statement behind partitioned / parallel aggregation. On the `TypedRelation`
(set) algebra, the combined table is `union` of the two shards. Because a set `union`
deduplicates, this needs the shards to be **disjoint** (which real partitions are — every row
lives in exactly one partition); `Finset.sum_union` then gives additivity.

## The two SQL queries being proved equivalent (partitions disjoint)

```sql
SELECT SUM(total_amount) FROM (orders_archive UNION orders_recent);
                                  ≡
(SELECT SUM(total_amount) FROM orders_archive) + (SELECT SUM(total_amount) FROM orders_recent);
```
-/

namespace Example6

abbrev ordCT : Fin 2 → Type := fun i => match i with | 0 => Nat | 1 => Int
instance : ∀ i, DecidableEq (ordCT i) := fun i => match i with | 0 => inferInstance | 1 => inferInstance

abbrev ordAmt : TypedTuple ordCT → Int := fun t => t 1

/-- `SELECT SUM(total_amount) FROM (archive UNION recent)`. -/
@[grind .]
def query_Whole (archive recent : TypedRelation ordCT) : Int :=
  ∑ t ∈ (union archive recent).rows, ordAmt t

/-- `(SELECT SUM … FROM archive) + (SELECT SUM … FROM recent)`. -/
@[grind .]
def query_Shards (archive recent : TypedRelation ordCT) : Int :=
  (∑ t ∈ archive.rows, ordAmt t) + (∑ t ∈ recent.rows, ordAmt t)

theorem query_equivalence (archive recent : TypedRelation ordCT)
    (h : Disjoint archive.rows recent.rows) :
    query_Whole archive recent = query_Shards archive recent := by
  simp only [query_Whole, query_Shards, union]
  grind +locals

end Example6
