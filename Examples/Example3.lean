import LeanDatabase.Aggregation
open LeanDatabase.Aggregation

/-!
# Example 3 — Correlated scalar subqueries ≡ GROUP BY + LEFT JOIN + COALESCE

The headline real-world rewrite: instead of running two correlated scalar subqueries *per
customer* (a nested-loop re-scan of `orders` for every customer), aggregate `orders` *once*
with `GROUP BY` and probe it with a `LEFT JOIN`, filling the misses with `COALESCE(_, 0)`.

## The two SQL queries being proved equivalent

```sql
-- query_Correlated: two correlated scalar subqueries per customer
SELECT c.customer_id, c.name,
       (SELECT COUNT(*)            FROM orders o WHERE o.customer_id = c.customer_id) AS order_count,
       (SELECT SUM(o.total_amount) FROM orders o WHERE o.customer_id = c.customer_id) AS total_spent
FROM customers c;

-- query_GroupJoin: aggregate once with GROUP BY, then LEFT JOIN + COALESCE
SELECT c.customer_id, c.name,
       COALESCE(o.order_count, 0) AS order_count,
       COALESCE(o.total_spent, 0) AS total_spent
FROM customers c
LEFT JOIN (
  SELECT customer_id, COUNT(*) AS order_count, SUM(total_amount) AS total_spent
  FROM orders
  GROUP BY customer_id
) o ON o.customer_id = c.customer_id;
```

NOTE on `SUM`/`NULL`: real SQL `SUM` over zero rows is `NULL`, so a customer with no orders
would get `NULL` from the correlated subquery — but the join side `COALESCE`s the miss to `0`.
We model "the value the user observes" as `COALESCE(SUM, 0)` on *both* sides (`bagSum` returns
`0` on the empty bag), so the two queries genuinely coincide, including that edge case.
-/

namespace Example3

/-! ## Schema -/

structure Customer where
  customer_id : Nat
  name : String
deriving DecidableEq, Repr

structure Order where
  customer_id : Nat
  total_amount : Int
deriving DecidableEq, Repr

structure CustomerSummary where
  customer_id : Nat
  name : String
  order_count : Nat
  total_spent : Int
deriving DecidableEq, Repr

structure OrderAgg where
  customer_id : Nat
  order_count : Nat
  total_spent : Int
deriving DecidableEq, Repr

/-! ## Queries -/

/-- Group key of an order. -/
abbrev ordKey : Order → Nat := (·.customer_id)

/-- `SELECT customer_id, COUNT(*), SUM(total_amount) ... GROUP BY customer_id` — per group. -/
def ordAgg (cid : Nat) (g : List Order) : OrderAgg :=
  { customer_id := cid, order_count := bagCount g, total_spent := bagSum (·.total_amount) g }

/-- The pre-aggregated `GROUP BY customer_id` subquery `o`. -/
def groupOrders (os : List Order) : List OrderAgg := groupBy ordKey ordAgg os

/-- Query 1: two correlated scalar subqueries per customer. -/
def query_Correlated (cs : List Customer) (os : List Order) : List CustomerSummary :=
  cs.map (fun c =>
    { customer_id := c.customer_id, name := c.name,
      order_count := bagCount (group ordKey c.customer_id os),
      total_spent := bagSum (·.total_amount) (group ordKey c.customer_id os) })

/-- Query 2: GROUP BY once, LEFT JOIN, then `COALESCE(_, 0)` the misses. -/
def query_GroupJoin (cs : List Customer) (os : List Order) : List CustomerSummary :=
  cs.map (fun c =>
    match lookup? (·.customer_id) c.customer_id (groupOrders os) with
    | some a => { customer_id := c.customer_id, name := c.name,
                  order_count := a.order_count, total_spent := a.total_spent }
    | none   => { customer_id := c.customer_id, name := c.name,
                  order_count := 0, total_spent := 0 })

theorem query_equivalence (cs : List Customer) (os : List Order) :
    query_Correlated cs os = query_GroupJoin cs os := by
  grind +locals

end Example3
