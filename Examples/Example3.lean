import LeanDatabase.SQLEquiv
open LeanDatabase

/-!
# Example 3 — Correlated scalar subqueries ≡ GROUP BY + LEFT JOIN + COALESCE

The headline rewrite, on the `TypedRelation` algebra: two correlated scalar subqueries
(`COUNT(*)`, `SUM(total_amount)`) per customer, vs. aggregate once with `GROUP BY` and probe
with a `LEFT JOIN` + `COALESCE(_, 0)`. Counts/sums are taken over the defined `restriction`
(`TypedAgg.cnt` / `TypedAgg.sumI`). Set semantics / dedup'd data.

## The two SQL queries being proved equivalent

```sql
-- query_Correlated:
SELECT c.customer_id, c.name,
       (SELECT COUNT(*)            FROM orders o WHERE o.customer_id = c.customer_id) AS order_count,
       (SELECT SUM(o.total_amount) FROM orders o WHERE o.customer_id = c.customer_id) AS total_spent
FROM customers c;

-- query_GroupJoin:
SELECT c.customer_id, c.name,
       COALESCE(o.order_count, 0) AS order_count,
       COALESCE(o.total_spent, 0) AS total_spent
FROM customers c
LEFT JOIN (SELECT customer_id, COUNT(*) AS order_count, SUM(total_amount) AS total_spent
           FROM orders GROUP BY customer_id) o
  ON o.customer_id = c.customer_id;
```
-/

namespace Example3

/-- `customers(customer_id : Nat, name : String)`. -/
abbrev custCT : Fin 2 → Type := fun i => match i with | 0 => Nat | 1 => String
/-- `orders(customer_id : Nat, total_amount : Int)`. -/
abbrev ordCT  : Fin 2 → Type := fun i => match i with | 0 => Nat | 1 => Int
/-- output `(customer_id : Nat, name : String, order_count : Nat, total_spent : Int)`. -/
abbrev outCT  : Fin 4 → Type := fun i => match i with | 0 => Nat | 1 => String | 2 => Nat | 3 => Int
instance : ∀ i, DecidableEq (custCT i) := fun i => match i with | 0 => inferInstance | 1 => inferInstance
instance : ∀ i, DecidableEq (ordCT i)  := fun i => match i with | 0 => inferInstance | 1 => inferInstance
instance : ∀ i, DecidableEq (outCT i)  := fun i =>
  match i with | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance | 3 => inferInstance

/-- `o.customer_id`. -/
abbrev ordKey : TypedTuple ordCT → Nat := fun t => t 0
/-- `o.total_amount`. -/
abbrev ordAmt : TypedTuple ordCT → Int := fun t => t 1

/-- An output row. -/
def out (id : Nat) (name : String) (c : Nat) (s : Int) : TypedTuple outCT :=
  fun j => match j with | 0 => id | 1 => name | 2 => c | 3 => s

/-- Query 1: two correlated scalar subqueries per customer. -/
def query_Correlated (customers : TypedRelation custCT) (orders : TypedRelation ordCT) :
    TypedRelation outCT :=
  { labels := fun j => match j with
      | 0 => customers.labels 0 | 1 => customers.labels 1 | 2 => "order_count" | 3 => "total_spent",
    rows := customers.rows.image (fun c =>
      out (c 0) (c 1) (cnt ordKey (c 0) orders) (sumI ordKey (c 0) orders ordAmt)) }

/-- Query 2: GROUP BY once, LEFT JOIN, `COALESCE(_, 0)` the misses. -/
def query_GroupJoin (customers : TypedRelation custCT) (orders : TypedRelation ordCT) :
    TypedRelation outCT :=
  { labels := fun j => match j with
      | 0 => customers.labels 0 | 1 => customers.labels 1 | 2 => "order_count" | 3 => "total_spent",
    rows := customers.rows.image (fun c =>
      out (c 0) (c 1)
        (if c 0 ∈ okeys ordKey orders then cnt ordKey (c 0) orders else 0)
        (if c 0 ∈ okeys ordKey orders then sumI ordKey (c 0) orders ordAmt else 0)) }

theorem query_equivalence (customers : TypedRelation custCT) (orders : TypedRelation ordCT) :
    query_Correlated customers orders = query_GroupJoin customers orders := by
  sql_equiv

end Example3
