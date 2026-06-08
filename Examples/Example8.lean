import LeanDatabase.Aggregation
open LeanDatabase.Aggregation

/-!
# Example 8 — `NOT IN` subquery ≡ `NOT EXISTS` (anti-join)

Both keep exactly the customers with no orders. The negative counterpart of the
`EXISTS`/`IN` semi-join (Example 5).

## The two SQL queries being proved equivalent

```sql
-- query_NotIn:
SELECT c.customer_id, c.name FROM customers c
WHERE c.customer_id NOT IN (SELECT o.customer_id FROM orders o);

-- query_NotExists:
SELECT c.customer_id, c.name FROM customers c
WHERE NOT EXISTS (SELECT 1 FROM orders o WHERE o.customer_id = c.customer_id);
```

(Note: real SQL `NOT IN` has a notorious three-valued-logic pitfall — if the subquery yields
any `NULL`, `NOT IN` returns no rows. We model the `NULL`-free case, where the two coincide.)
-/

namespace Example8

structure Customer where
  customer_id : Nat
  name : String
deriving DecidableEq, Repr

structure Order where
  customer_id : Nat
  total_amount : Int
deriving DecidableEq, Repr

/-- Group key of an order. -/
abbrev ordKey : Order → Nat := (·.customer_id)

/-- `... WHERE c.customer_id NOT IN (SELECT customer_id FROM orders)`. -/
def query_NotIn (cs : List Customer) (os : List Order) : List Customer :=
  cs.filter (fun c => decide (c.customer_id ∉ keys ordKey os))

/-- `... WHERE NOT EXISTS (SELECT 1 FROM orders o WHERE o.customer_id = c.customer_id)`. -/
def query_NotExists (cs : List Customer) (os : List Order) : List Customer :=
  cs.filter (fun c => decide (group ordKey c.customer_id os = []))

theorem query_equivalence (cs : List Customer) (os : List Order) :
    query_NotIn cs os = query_NotExists cs os := by
  grind +locals

end Example8
