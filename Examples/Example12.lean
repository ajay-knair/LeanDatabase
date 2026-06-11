import LeanDatabase.SQLEquiv

open LeanDatabase

/-!
# Example 12 — `SUM(CASE…)` + `HAVING` ≡ `WHERE` + `SUM` + `HAVING`

Filtering inside the aggregate with `CASE` equals filtering rows with `WHERE` before
aggregating — so the planner may push `status = 'completed'` into a `WHERE`.

## The two SQL queries being proved equivalent

```sql
SELECT customer_id,
       SUM(CASE WHEN status = 'completed' THEN total_amount ELSE 0 END) AS completed_total
FROM orders GROUP BY customer_id
HAVING SUM(CASE WHEN status = 'completed' THEN total_amount ELSE 0 END) > 1000;
                                  ≡
SELECT customer_id, SUM(total_amount) AS completed_total
FROM orders WHERE status = 'completed' GROUP BY customer_id
HAVING SUM(total_amount) > 1000;
```

The whole-result equality is *set-level* (the two `GROUP BY`s scan different relations, so row
order is unspecified — fine for SQL). Its entire content is the **per-customer-group** identity
below, on the `TypedRelation` algebra: the `CASE`-`SUM` over a group equals the plain `SUM` over
that group's `WHERE`-`restriction`. The `HAVING > 1000` test, applied to equal values, then
agrees too.
-/

namespace Example12

/-- `orders(customer_id : Nat, status : String, total_amount : Int)`. -/
abbrev ordCT : Fin 3 → Type := fun i => match i with | 0 => Nat | 1 => String | 2 => Int
instance : ∀ i, DecidableEq (ordCT i) := fun i =>
  match i with | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance

abbrev ordKey : TypedTuple ordCT → Nat := fun t => t 0
abbrev isCompleted : TypedTuple ordCT → Bool := fun t => t 1 == "completed"
abbrev amount : TypedTuple ordCT → Int := fun t => t 2

/-- query 1's `completed_total` for a group: `SUM(CASE WHEN completed THEN amt ELSE 0)`. -/
def total_CaseSum (orders : TypedRelation ordCT) (k : Nat) : Int :=
  ∑ t ∈ (grp ordKey k orders).rows, (if isCompleted t then amount t else 0)

/-- query 2's `completed_total`: `SUM(amt)` over the group's `WHERE completed` restriction. -/
def total_WhereSum (orders : TypedRelation ordCT) (k : Nat) : Int :=
  ∑ t ∈ (restriction isCompleted (grp ordKey k orders)).rows, amount t

/-- The rewrite, per customer group: the two `completed_total`s agree, hence so do the
    `SELECT` value and the `HAVING ... > 1000` test. -/
theorem query_equivalence (orders : TypedRelation ordCT) (k : Nat) :
    total_CaseSum orders k = total_WhereSum orders k ∧
    (decide (total_CaseSum orders k > 1000) = decide (total_WhereSum orders k > 1000)) := by
  sql_equiv

end Example12
