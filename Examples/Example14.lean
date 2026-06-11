import LeanDatabase.SQLEquiv
open LeanDatabase

/-!
# Example 14 — predicate pushdown through a semi-join

`σ_p(R ⋉ S) = (σ_p R) ⋉ S` — a `WHERE` on a semi-join (`EXISTS`/`IN`) can be pushed onto the
left relation before the semi-join (a real optimizer rewrite). Uses `semijoin` + `restriction`.

```sql
SELECT * FROM R WHERE p(R) AND     EXISTS (SELECT * FROM S WHERE S.b = R.b);
SELECT * FROM (SELECT * FROM R WHERE p(R)) R WHERE EXISTS (SELECT * FROM S WHERE S.b = R.b);
```
-/

namespace Example14

abbrev rCT : Fin 2 → Type := fun i => match i with | 0 => Nat | 1 => Nat
abbrev sCT : Fin 2 → Type := fun i => match i with | 0 => Nat | 1 => Nat
instance : ∀ i, DecidableEq (rCT i) := fun i => match i with | 0 => inferInstance | 1 => inferInstance
instance : ∀ i, DecidableEq (sCT i) := fun i => match i with | 0 => inferInstance | 1 => inferInstance

/-- join/`EXISTS` condition `R.b = S.b`. -/
abbrev cond (r : TypedTuple rCT) (s : TypedTuple sCT) : Bool := decide (r 1 = s 0)

/-- `σ_p (R ⋉ S)` — filter the semi-join. -/
@[simp] def query_FilterAfter (p : TypedTuple rCT → Bool) (R : TypedRelation rCT) (S : TypedRelation sCT) :
    TypedRelation rCT :=
  restriction p (semijoin R S cond)

/-- `(σ_p R) ⋉ S` — push the filter onto `R` first. -/
@[simp] def query_FilterBefore (p : TypedTuple rCT → Bool) (R : TypedRelation rCT) (S : TypedRelation sCT) :
    TypedRelation rCT :=
  semijoin (restriction p R) S cond

theorem query_equivalence (p : TypedTuple rCT → Bool)
    (R : TypedRelation rCT) (S : TypedRelation sCT) :
    query_FilterAfter p R S = query_FilterBefore p R S := by
  sql_equiv

end Example14
