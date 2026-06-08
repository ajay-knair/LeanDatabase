import LeanDatabase.Aggregation
open LeanDatabase.Aggregation

/-!
# Example 11 — "latest row per group": `MAX` self-join ≡ `NOT EXISTS` a-later-row

The "greatest-N-per-group" rewrite. The user's original pair was `ROW_NUMBER() = 1` vs the
`MAX` self-join — but those are **not** equivalent on ties: `ROW_NUMBER = 1` returns exactly
one row per customer (ties broken arbitrarily), whereas the `MAX` self-join returns *every*
row hitting the group maximum. So instead we prove the **unconditionally equivalent** rewrite
of the `MAX` self-join: keep an order iff **no later order exists** for the same customer
(`NOT EXISTS`). Both keep all rows tied at the maximum `created_at`, with no ties caveat.

## The two SQL queries being proved equivalent

```sql
-- query_MaxJoin: join each order to its group's MAX(created_at)
SELECT o.*
FROM orders o
JOIN (SELECT customer_id, MAX(created_at) AS latest FROM orders GROUP BY customer_id) m
  ON m.customer_id = o.customer_id AND m.latest = o.created_at;

-- query_NotExistsLater: keep o unless a strictly later order of the same customer exists
SELECT o.*
FROM orders o
WHERE NOT EXISTS (
  SELECT 1 FROM orders o2
  WHERE o2.customer_id = o.customer_id AND o2.created_at > o.created_at
);
```
-/

namespace Example11

structure Order where
  customer_id : Nat
  created_at : Nat
  amount : Int
deriving DecidableEq, Repr

/-- Group key of an order. -/
abbrev ordKey : Order → Nat := (·.customer_id)

/-- `JOIN (SELECT customer_id, MAX(created_at) …) m ON … AND m.latest = o.created_at`:
    keep orders whose `created_at` equals their group's `MAX(created_at)`. -/
def query_MaxJoin (os : List Order) : List Order :=
  os.filter (fun o => decide (o.created_at = groupMaxBy ordKey (·.created_at) o.customer_id os))

/-- `WHERE NOT EXISTS (… o2.customer_id = o.customer_id AND o2.created_at > o.created_at)`. -/
def query_NotExistsLater (os : List Order) : List Order :=
  os.filter (fun o =>
    decide (¬ ∃ o2 ∈ group ordKey o.customer_id os, o.created_at < o2.created_at))

theorem query_equivalence (os : List Order) :
    query_MaxJoin os = query_NotExistsLater os := by
  grind +locals

end Example11
