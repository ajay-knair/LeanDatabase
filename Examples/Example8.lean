import LeanDatabase.TypedAggregation
open LeanDatabase LeanDatabase.TypedAgg

/-!
# Example 8 — `NOT IN` ≡ `NOT EXISTS` (anti-join)

Keep the customers with no orders. The negative counterpart of Example 5; both are a
`restriction` of `customers` whose predicates agree by `TypedAgg.grp_nonempty_iff`.
(NULL-free / dedup'd data, so the real-SQL `NOT IN` NULL pitfall does not arise.)

## The two SQL queries being proved equivalent

```sql
SELECT * FROM customers c WHERE c.customer_id NOT IN (SELECT customer_id FROM orders);
SELECT * FROM customers c WHERE NOT EXISTS (SELECT 1 FROM orders o WHERE o.customer_id = c.customer_id);
```
-/

namespace Example8

abbrev custCT : Fin 2 → Type := fun i => match i with | 0 => Nat | 1 => String
abbrev ordCT  : Fin 2 → Type := fun i => match i with | 0 => Nat | 1 => Int
instance : ∀ i, DecidableEq (custCT i) := fun i => match i with | 0 => inferInstance | 1 => inferInstance
instance : ∀ i, DecidableEq (ordCT i)  := fun i => match i with | 0 => inferInstance | 1 => inferInstance

abbrev ordKey : TypedTuple ordCT → Nat := fun t => t 0

/-- `... WHERE c.customer_id NOT IN (SELECT customer_id FROM orders)`. -/
def query_NotIn (customers : TypedRelation custCT) (orders : TypedRelation ordCT) :
    TypedRelation custCT :=
  restriction (fun c => decide (c 0 ∉ okeys ordKey orders)) customers

/-- `... WHERE NOT EXISTS (SELECT 1 FROM orders o WHERE o.customer_id = c.customer_id)`. -/
def query_NotExists (customers : TypedRelation custCT) (orders : TypedRelation ordCT) :
    TypedRelation custCT :=
  restriction (fun c => decide ¬ (grp ordKey (c 0) orders).rows.Nonempty) customers

theorem query_equivalence (customers : TypedRelation custCT) (orders : TypedRelation ordCT) :
    query_NotIn customers orders = query_NotExists customers orders := by
  sql_equiv

end Example8
