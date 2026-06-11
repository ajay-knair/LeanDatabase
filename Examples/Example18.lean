import LeanDatabase.SQLEquiv
open LeanDatabase

/-!
# Example 18 — `ORDER BY` + `LIMIT` + `LIKE`

Three of the order/pattern features at once. `WHERE name LIKE '%'` keeps every row (the lone `%`
matches anything), and under set semantics `ORDER BY` and `LIMIT` are no-ops on the row-set — so
the whole query collapses to `R`:

```sql
SELECT * FROM R WHERE name LIKE '%' ORDER BY age LIMIT n   ≡   SELECT * FROM R
```
(`ORDER BY`/`LIMIT` only affect *presentation*/cardinality, which set-equivalence ignores; see
`orderBy_eq` / `limit_eq`.)
-/

namespace Example18

abbrev rCT : Fin 2 → Type := fun i => match i with | 0 => String | 1 => Nat
instance : ∀ i, DecidableEq (rCT i) := fun i => match i with | 0 => inferInstance | 1 => inferInstance

theorem query_equivalence (n : Nat) (key : TypedTuple rCT → Nat) (R : TypedRelation rCT) :
    limit n (orderBy key (restriction (colLike (fun t => t 0) "%") R)) = R := by
  sql_equiv

end Example18
