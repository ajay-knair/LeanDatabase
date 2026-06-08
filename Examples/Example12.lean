import LeanDatabase.Aggregation
open LeanDatabase.Aggregation

/-!
# Example 12 — `SUM(CASE…)` + `HAVING` ≡ `WHERE` + `SUM` + `HAVING`

Filtering inside the aggregate with `CASE` is the same as filtering the rows with `WHERE`
before aggregating — so the planner may push `status = 'completed'` down into a `WHERE`.

## The two SQL queries being proved equivalent

```sql
-- query_CaseHaving: filter inside the aggregate with CASE, group over all orders
SELECT customer_id,
       SUM(CASE WHEN status = 'completed' THEN total_amount ELSE 0 END) AS completed_total
FROM orders
GROUP BY customer_id
HAVING SUM(CASE WHEN status = 'completed' THEN total_amount ELSE 0 END) > 1000;

-- query_WhereHaving: push the filter into a WHERE, then plain SUM
SELECT customer_id,
       SUM(total_amount) AS completed_total
FROM orders
WHERE status = 'completed'
GROUP BY customer_id
HAVING SUM(total_amount) > 1000;
```

Query 1 groups over *all* orders while query 2 groups over the *completed* orders, so the two
`GROUP BY`s emit their rows in different order. SQL leaves `GROUP BY` output order unspecified,
so the right notion of equivalence is "same rows up to reordering" — `List.Perm` (`~`).
-/

namespace Example12

structure Order where
  customer_id : Nat
  status : String
  total_amount : Int
deriving DecidableEq, Repr

structure ResultRow where
  customer_id : Nat
  completed_total : Int
deriving DecidableEq, Repr

/-- Group key of an order. -/
abbrev ordKey : Order → Nat := (·.customer_id)

/-- `status = 'completed'` as a `Bool` predicate. -/
abbrev isCompleted : Order → Bool := (·.status == "completed")

/-- query 1's aggregate: `SUM(CASE WHEN completed THEN total ELSE 0)`. -/
def aggCase (cid : Nat) (g : List Order) : ResultRow :=
  { customer_id := cid, completed_total := bagSum (caseSum isCompleted (·.total_amount)) g }

/-- query 2's aggregate: `SUM(total)` over the already-`WHERE`-filtered group. -/
def aggSum (cid : Nat) (g : List Order) : ResultRow :=
  { customer_id := cid, completed_total := bagSum (·.total_amount) g }

/-- Query 1: `SUM(CASE…)` over all orders grouped by customer, `HAVING > 1000`. -/
def query_CaseHaving (os : List Order) : List ResultRow :=
  (groupBy ordKey aggCase os).filter (fun r => decide (r.completed_total > 1000))

/-- Query 2: `WHERE completed`, `SUM(total)` grouped by customer, `HAVING > 1000`. -/
def query_WhereHaving (os : List Order) : List ResultRow :=
  (groupBy ordKey aggSum (os.filter isCompleted)).filter (fun r => decide (r.completed_total > 1000))

/-
THIS DOES NOT WORK just with `grind`.
-/

theorem query_equivalence (os : List Order) :
    (query_CaseHaving os).Perm (query_WhereHaving os) := by
  refine (List.perm_ext_iff_of_nodup ?_ ?_).mpr ?_
  · exact (groupBy_nodup ordKey (·.customer_id) aggCase (fun _ _ => rfl) os).filter _
  · exact (groupBy_nodup ordKey (·.customer_id) aggSum (fun _ _ => rfl) _).filter _
  · intro r
    simp only [query_CaseHaving, query_WhereHaving, List.mem_filter,
      mem_groupBy ordKey (·.customer_id) aggCase (fun _ _ => rfl),
      mem_groupBy ordKey (·.customer_id) aggSum (fun _ _ => rfl), group_filter,
      aggCase, aggSum]
    grind

end Example12
