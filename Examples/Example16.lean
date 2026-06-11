import LeanDatabase.SQLEquiv
open LeanDatabase

/-!
# Example 16 — `SELECT f DISTINCT (WHERE q (WHERE p))` ≡ `SELECT f (WHERE p AND q)`

Combines computed `SELECT` (`select`), `DISTINCT` (a no-op on a set), and cascaded `WHERE`
(two filters collapse to one `AND`).

```sql
SELECT DISTINCT g(R) FROM (SELECT * FROM (SELECT * FROM R WHERE q) WHERE p)
≡  SELECT g(R) FROM R WHERE p AND q
```
-/

namespace Example16

abbrev rCT : Fin 2 → Type := fun i => match i with | 0 => Nat | 1 => Nat
abbrev oCT : Fin 1 → Type := fun _ => Nat
instance : ∀ i, DecidableEq (rCT i) := fun i => match i with | 0 => inferInstance | 1 => inferInstance
instance : ∀ i, DecidableEq (oCT i) := fun _ => inferInstance

/-- a computed output row, e.g. `SELECT a + b`. -/
abbrev g (t : TypedTuple rCT) : TypedTuple oCT := fun _ => t 0 + t 1

@[simp] def query_Nested (p q : TypedTuple rCT → Bool) (R : TypedRelation rCT) : TypedRelation oCT :=
  select (fun _ => "g") g (distinct (restriction p (restriction q R)))

@[simp] def query_Flat (p q : TypedTuple rCT → Bool) (R : TypedRelation rCT) : TypedRelation oCT :=
  select (fun _ => "g") g (restriction (fun t => p t && q t) R)

theorem query_equivalence (p q : TypedTuple rCT → Bool) (R : TypedRelation rCT) :
    query_Nested p q R = query_Flat p q R := by
  sql_equiv

end Example16
