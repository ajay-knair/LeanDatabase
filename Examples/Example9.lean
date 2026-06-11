import LeanDatabase.SQLEquiv
open LeanDatabase

/-!
# Example 9 — `LEFT JOIN … WHERE right IS NULL` ≡ `NOT EXISTS` (anti-join)

The outer-join anti-join idiom. On the `TypedRelation` algebra both are a `restriction` of
`customers`: the `LEFT JOIN` probe is `NULL` exactly when the customer's id is absent from the
order keys (`c.customer_id ∉ okeys`), which by `TypedAgg.grp_nonempty_iff` is the same as the
`NOT EXISTS` group being empty.

## The two SQL queries being proved equivalent

```sql
SELECT c.* FROM customers c
LEFT JOIN orders o ON o.customer_id = c.customer_id
WHERE o.customer_id IS NULL;

SELECT c.* FROM customers c
WHERE NOT EXISTS (SELECT 1 FROM orders o WHERE o.customer_id = c.customer_id);
```
-/

namespace Example9

abbrev custCT : Fin 2 → Type := fun i => match i with | 0 => Nat | 1 => String
abbrev ordCT  : Fin 2 → Type := fun i => match i with | 0 => Nat | 1 => Int
instance : ∀ i, DecidableEq (custCT i) := fun i => match i with | 0 => inferInstance | 1 => inferInstance
instance : ∀ i, DecidableEq (ordCT i)  := fun i => match i with | 0 => inferInstance | 1 => inferInstance

abbrev ordKey : TypedTuple ordCT → Nat := fun t => t 0

/-- `LEFT JOIN orders … WHERE o.customer_id IS NULL`: the join probe found no order key. -/
def query_LeftJoinNull (customers : TypedRelation custCT) (orders : TypedRelation ordCT) :
    TypedRelation custCT :=
  restriction (fun c => decide (c 0 ∉ okeys ordKey orders)) customers

/-- `WHERE NOT EXISTS (SELECT 1 FROM orders o WHERE o.customer_id = c.customer_id)`. -/
def query_NotExists (customers : TypedRelation custCT) (orders : TypedRelation ordCT) :
    TypedRelation custCT :=
  restriction (fun c => decide ¬ (grp ordKey (c 0) orders).rows.Nonempty) customers

theorem query_equivalence (customers : TypedRelation custCT) (orders : TypedRelation ordCT) :
    query_LeftJoinNull customers orders = query_NotExists customers orders := by
  sql_equiv

end Example9
