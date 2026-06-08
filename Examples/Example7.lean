import LeanDatabase.Aggregation
open LeanDatabase.Aggregation

/-!
# Example 7 — Correlated `COUNT(*)` subquery ≡ GROUP BY + LEFT JOIN + COALESCE

The `COUNT`-only version of the per-customer order-count report: run a correlated `COUNT(*)`
subquery per customer, vs. aggregate once with `GROUP BY` and `LEFT JOIN` + `COALESCE(_, 0)`.

## The two SQL queries being proved equivalent

```sql
-- query_Correlated:
SELECT c.customer_id, c.name,
       (SELECT COUNT(*) FROM orders o WHERE o.customer_id = c.customer_id) AS order_count
FROM customers c;

-- query_GroupJoin:
SELECT c.customer_id, c.name, COALESCE(o.order_count, 0) AS order_count
FROM customers c
LEFT JOIN (
  SELECT customer_id, COUNT(*) AS order_count
  FROM orders
  GROUP BY customer_id
) o ON o.customer_id = c.customer_id;
```
-/

namespace Example7

structure Customer where
  customer_id : Nat
  name : String
deriving DecidableEq, Repr

structure Order where
  customer_id : Nat
  total_amount : Int
deriving DecidableEq, Repr

structure CustomerCount where
  customer_id : Nat
  name : String
  order_count : Nat
deriving DecidableEq, Repr

structure OrderAgg where
  customer_id : Nat
  order_count : Nat
deriving DecidableEq, Repr

/-- Group key of an order. -/
abbrev ordKey : Order → Nat := (·.customer_id)

/-- `SELECT customer_id, COUNT(*) ... GROUP BY customer_id` — per group. -/
def ordAgg (cid : Nat) (g : List Order) : OrderAgg :=
  { customer_id := cid, order_count := bagCount g }

/-- The pre-aggregated `GROUP BY customer_id` subquery `o`. -/
def groupOrders (os : List Order) : List OrderAgg := groupBy ordKey ordAgg os

/-- Query 1: one correlated `COUNT(*)` subquery per customer. -/
def query_Correlated (cs : List Customer) (os : List Order) : List CustomerCount :=
  cs.map (fun c =>
    { customer_id := c.customer_id, name := c.name,
      order_count := bagCount (group ordKey c.customer_id os) })

/-- Query 2: GROUP BY once, LEFT JOIN, `COALESCE(_, 0)` the misses. -/
def query_GroupJoin (cs : List Customer) (os : List Order) : List CustomerCount :=
  cs.map (fun c =>
    match lookup? (·.customer_id) c.customer_id (groupOrders os) with
    | some a => { customer_id := c.customer_id, name := c.name, order_count := a.order_count }
    | none   => { customer_id := c.customer_id, name := c.name, order_count := 0 })

theorem query_equivalence (cs : List Customer) (os : List Order) :
    query_Correlated cs os = query_GroupJoin cs os := by
  grind +locals

end Example7
