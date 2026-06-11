import LeanDatabase.SQLEquiv
open LeanDatabase

/-!
# Example 17 — `COUNT(WHERE p) + COUNT(WHERE NOT p) = COUNT(*)`

A whole-relation `COUNT` splits across a predicate and its negation. Uses the ungrouped
aggregate `relCount`.

```sql
(SELECT COUNT(*) FROM R WHERE p) + (SELECT COUNT(*) FROM R WHERE NOT p)
≡  SELECT COUNT(*) FROM R
```
-/

namespace Example17

abbrev rCT : Fin 2 → Type := fun i => match i with | 0 => Nat | 1 => Nat
instance : ∀ i, DecidableEq (rCT i) := fun i => match i with | 0 => inferInstance | 1 => inferInstance

theorem query_equivalence (p : TypedTuple rCT → Bool) (R : TypedRelation rCT) :
    relCount (restriction p R) + relCount (restriction (fun t => !p t) R) = relCount R := by
  sql_equiv

end Example17
