import LeanDatabase.Aggregation
open LeanDatabase.Aggregation

/-!
# Example 6 — Partitioned aggregation ≡ summing per-shard partial aggregates

Aggregating one combined table equals aggregating each partition independently and adding the
partials. This is the correctness statement behind partitioned / parallel / map-reduce
aggregation and aggregation over a `UNION ALL` of shards.

## The two SQL queries being proved equivalent

```sql
-- query_Whole: aggregate the whole (UNION ALL of the two shards)
SELECT SUM(total_amount) FROM (
  SELECT * FROM orders_archive
  UNION ALL
  SELECT * FROM orders_recent
);

-- query_Shards: aggregate each shard, then add the partials
SELECT (SELECT SUM(total_amount) FROM orders_archive)
     + (SELECT SUM(total_amount) FROM orders_recent);
```
-/

namespace Example6

structure Order where
  customer_id : Nat
  total_amount : Int
deriving DecidableEq, Repr

/-- `SELECT SUM(total_amount) FROM (archive UNION ALL recent)`. -/
def query_Whole (archive recent : List Order) : Int :=
  bagSum (·.total_amount) (archive ++ recent)

/-- `(SELECT SUM(total_amount) FROM archive) + (SELECT SUM(total_amount) FROM recent)`. -/
def query_Shards (archive recent : List Order) : Int :=
  bagSum (·.total_amount) archive + bagSum (·.total_amount) recent

theorem query_equivalence (archive recent : List Order) :
    query_Whole archive recent = query_Shards archive recent := by
  grind +locals

end Example6
