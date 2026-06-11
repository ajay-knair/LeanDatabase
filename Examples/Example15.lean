import LeanDatabase.SQLEquiv
open LeanDatabase

/-!
# Example 15 — `(R ⋉ S) ∪ (R ▷ S) = R` (semi/anti-join partition)

Every left row either has a matching right row (semi-join) or does not (anti-join), so unioning
the two gives back `R`. Uses `semijoin` + `antijoin` + `union`.

```sql
(SELECT * FROM R WHERE     EXISTS (SELECT * FROM S WHERE S.b = R.b))
UNION
(SELECT * FROM R WHERE NOT EXISTS (SELECT * FROM S WHERE S.b = R.b))
≡  SELECT * FROM R
```
-/

namespace Example15

abbrev rCT : Fin 2 → Type := fun i => match i with | 0 => Nat | 1 => Nat
abbrev sCT : Fin 2 → Type := fun i => match i with | 0 => Nat | 1 => Nat
instance : ∀ i, DecidableEq (rCT i) := fun i => match i with | 0 => inferInstance | 1 => inferInstance
instance : ∀ i, DecidableEq (sCT i) := fun i => match i with | 0 => inferInstance | 1 => inferInstance

abbrev cond (r : TypedTuple rCT) (s : TypedTuple sCT) : Bool := decide (r 1 = s 0)

@[simp] def query_Split (R : TypedRelation rCT) (S : TypedRelation sCT) : TypedRelation rCT :=
  union (semijoin R S cond) (antijoin R S cond)

theorem query_equivalence (R : TypedRelation rCT) (S : TypedRelation sCT) :
    query_Split R S = R := by
  sql_equiv

end Example15
