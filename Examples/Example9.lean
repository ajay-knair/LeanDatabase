import LeanDatabase.Aggregation
open LeanDatabase.Aggregation

/-!
# Example 9 — `LEFT JOIN … WHERE right IS NULL` ≡ `NOT EXISTS` (anti-join)

The "anti-join via outer join" idiom: `LEFT JOIN` customers to orders, then keep only the
rows where the order side came back `NULL` (no match). That equals `NOT EXISTS`.

## The two SQL queries being proved equivalent

```sql
-- query_LeftJoinNull:
SELECT c.customer_id, c.name
FROM customers c
LEFT JOIN orders o ON o.customer_id = c.customer_id
WHERE o.customer_id IS NULL;

-- query_NotExists:
SELECT c.customer_id, c.name
FROM customers c
WHERE NOT EXISTS (SELECT 1 FROM orders o WHERE o.customer_id = c.customer_id);
```

We model the `LEFT JOIN ... WHERE o IS NULL` by its surviving-rows semantics: probe the
orders side for each customer (`lookup?` into the grouped order keys = the join), and keep the
customer exactly when that probe is `NULL` (`isNone`, i.e. no matching order). This keeps the
same set of customers as the raw outer join + `IS NULL`, while staying within the
`filter`/`lookup` machinery.
-/

namespace Example9

structure Customer where
  customer_id : Nat
  name : String
deriving DecidableEq, Repr

structure Order where
  customer_id : Nat
  total_amount : Int
deriving DecidableEq, Repr

structure OrderKey where
  customer_id : Nat
deriving DecidableEq, Repr

/-- Group key of an order. -/
abbrev ordKey : Order → Nat := (·.customer_id)

/-- The distinct order customer ids, as a `GROUP BY customer_id` subquery to join against. -/
def ordAgg (cid : Nat) (_g : List Order) : OrderKey := { customer_id := cid }

def groupOrders (os : List Order) : List OrderKey := groupBy ordKey ordAgg os

/-- `LEFT JOIN orders o ON o.customer_id = c.customer_id WHERE o.customer_id IS NULL`:
    keep customers whose join probe is `NULL`. -/
def query_LeftJoinNull (cs : List Customer) (os : List Order) : List Customer :=
  cs.filter (fun c => (lookup? (·.customer_id) c.customer_id (groupOrders os)).isNone)

/-- `... WHERE NOT EXISTS (SELECT 1 FROM orders o WHERE o.customer_id = c.customer_id)`. -/
def query_NotExists (cs : List Customer) (os : List Order) : List Customer :=
  cs.filter (fun c => decide (group ordKey c.customer_id os = []))

theorem query_equivalence (cs : List Customer) (os : List Order) :
    query_LeftJoinNull cs os = query_NotExists cs os := by
  grind +locals

end Example9
