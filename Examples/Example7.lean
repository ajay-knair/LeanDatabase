import LeanDatabase.TypedAggregation
open LeanDatabase LeanDatabase.TypedAgg

/-!
# Example 7 — Correlated `COUNT(*)` ≡ GROUP BY + LEFT JOIN + COALESCE

Built on the `TypedRelation` relational algebra (rows are `TypedTuple`s; the per-customer
filter is the defined `restriction`, via `TypedAgg.cnt`). Set semantics / dedup'd data.

## The two SQL queries being proved equivalent

```sql
-- query_Correlated:
SELECT c.customer_id, c.name,
       (SELECT COUNT(*) FROM orders o WHERE o.customer_id = c.customer_id) AS order_count
FROM customers c;

-- query_GroupJoin:
SELECT c.customer_id, c.name, COALESCE(o.order_count, 0) AS order_count
FROM customers c
LEFT JOIN (SELECT customer_id, COUNT(*) AS order_count FROM orders GROUP BY customer_id) o
  ON o.customer_id = c.customer_id;
```
-/

namespace Example7

/-- `customers(customer_id : Nat, name : String)`. -/
abbrev custCT : Fin 2 → Type := fun i => match i with | 0 => Nat | 1 => String
/-- `orders(customer_id : Nat, total_amount : Int)`. -/
abbrev ordCT  : Fin 2 → Type := fun i => match i with | 0 => Nat | 1 => Int
/-- output `(customer_id : Nat, name : String, order_count : Nat)`. -/
abbrev outCT  : Fin 3 → Type := fun i => match i with | 0 => Nat | 1 => String | 2 => Nat
instance : ∀ i, DecidableEq (custCT i) := fun i => match i with | 0 => inferInstance | 1 => inferInstance
instance : ∀ i, DecidableEq (ordCT i)  := fun i => match i with | 0 => inferInstance | 1 => inferInstance
instance : ∀ i, DecidableEq (outCT i)  := fun i => match i with | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance

/-- `o.customer_id`. -/
abbrev ordKey : TypedTuple ordCT → Nat := fun t => t 0

/-- An output row. -/
def out (id : Nat) (name : String) (c : Nat) : TypedTuple outCT :=
  fun j => match j with | 0 => id | 1 => name | 2 => c

/-- Query 1: correlated `COUNT(*)` per customer (count via the defined `restriction`). -/
def query_Correlated (customers : TypedRelation custCT) (orders : TypedRelation ordCT) :
    TypedRelation outCT :=
  { labels := fun j => match j with | 0 => customers.labels 0 | 1 => customers.labels 1 | 2 => "order_count",
    rows := customers.rows.image (fun c => out (c 0) (c 1) (cnt ordKey (c 0) orders)) }

/-- Query 2: GROUP BY once, LEFT JOIN, `COALESCE(_, 0)` the misses. -/
def query_GroupJoin (customers : TypedRelation custCT) (orders : TypedRelation ordCT) :
    TypedRelation outCT :=
  { labels := fun j => match j with | 0 => customers.labels 0 | 1 => customers.labels 1 | 2 => "order_count",
    rows := customers.rows.image (fun c =>
      out (c 0) (c 1) (if c 0 ∈ okeys ordKey orders then cnt ordKey (c 0) orders else 0)) }

theorem query_equivalence (customers : TypedRelation custCT) (orders : TypedRelation ordCT) :
    query_Correlated customers orders = query_GroupJoin customers orders := by
  grind +locals

end Example7
