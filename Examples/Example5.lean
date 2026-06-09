import LeanDatabase.TypedAggregation
open LeanDatabase LeanDatabase.TypedAgg

/-!
# Example 5 — `EXISTS` correlated subquery ≡ `IN` subquery (semi-join)

Keep the customers that have at least one order. On the `TypedRelation` algebra: both queries
are a `restriction` of `customers`; the predicates agree by `TypedAgg.grp_nonempty_iff`
("a customer's order group is non-empty iff its id occurs among order keys").

## The two SQL queries being proved equivalent

```sql
SELECT * FROM customers c WHERE EXISTS (SELECT 1 FROM orders o WHERE o.customer_id = c.customer_id);
SELECT * FROM customers c WHERE c.customer_id IN (SELECT customer_id FROM orders);
```
-/

namespace Example5

abbrev custCT : Fin 2 → Type := fun i => match i with | 0 => Nat | 1 => String
abbrev ordCT  : Fin 2 → Type := fun i => match i with | 0 => Nat | 1 => Int
instance : ∀ i, DecidableEq (custCT i) := fun i => match i with | 0 => inferInstance | 1 => inferInstance
instance : ∀ i, DecidableEq (ordCT i)  := fun i => match i with | 0 => inferInstance | 1 => inferInstance

abbrev ordKey : TypedTuple ordCT → Nat := fun t => t 0

/-- `... WHERE EXISTS (SELECT 1 FROM orders o WHERE o.customer_id = c.customer_id)`. -/
def query_Exists (customers : TypedRelation custCT) (orders : TypedRelation ordCT) :
    TypedRelation custCT :=
  restriction (fun c => decide (grp ordKey (c 0) orders).rows.Nonempty) customers

/-- `... WHERE c.customer_id IN (SELECT customer_id FROM orders)`. -/
def query_In (customers : TypedRelation custCT) (orders : TypedRelation ordCT) :
    TypedRelation custCT :=
  restriction (fun c => decide (c 0 ∈ okeys ordKey orders)) customers

theorem query_equivalence (customers : TypedRelation custCT) (orders : TypedRelation ordCT) :
    query_Exists customers orders = query_In customers orders := by
  sql_equiv

end Example5
