import LeanDatabase.Aggregation
open LeanDatabase.Aggregation

/-!
# Example 5 — `EXISTS` correlated subquery ≡ `IN` subquery (semi-join)

Both queries keep exactly the customers that have at least one order. The classic
"`EXISTS (correlated subquery)` and `key IN (subquery)` describe the same semi-join" rewrite.

## The two SQL queries being proved equivalent

```sql
-- query_Exists: correlated EXISTS
SELECT * FROM customers c
WHERE EXISTS (SELECT 1 FROM orders o WHERE o.customer_id = c.customer_id);

-- query_In: IN subquery
SELECT * FROM customers c
WHERE c.customer_id IN (SELECT customer_id FROM orders);
```
-/

namespace Example5

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

/-- `... WHERE EXISTS (SELECT 1 FROM orders o WHERE o.customer_id = c.customer_id)`. -/
def query_Exists (cs : List Customer) (os : List Order) : List Customer :=
  cs.filter (fun c => decide (group ordKey c.customer_id os ≠ []))

/-- `... WHERE c.customer_id IN (SELECT customer_id FROM orders)`. -/
def query_In (cs : List Customer) (os : List Order) : List Customer :=
  cs.filter (fun c => decide (c.customer_id ∈ keys ordKey os))

theorem query_equivalence (cs : List Customer) (os : List Order) :
    query_Exists cs os = query_In cs os := by
  grind +locals

end Example5
