import LeanDatabase.SQLEquiv

open LeanDatabase

/-!
# Example 13 — toolbox demo: equivalences that close "for free"

Each equivalence below needs a lemma that isn't specific to the example — they live in
`LeanDatabase.SQLToolbox` (set-algebra rewrites) and `LeanDatabase.Operators.Aggregate`
(aggregation/coalesce). Importing the toolbox lets every query equivalence here close with a
bare `grind +locals`, on the `TypedRelation` algebra.
-/

namespace Example13

variable {n : Nat} {colType : Fin n → Type} [∀ i, DecidableEq (colType i)]
set_option linter.unusedSectionVars false

/-- `SELECT * FROM (a INTERSECT b) WHERE p ≡ (a WHERE p) INTERSECT (b WHERE p)`. -/
theorem select_inter (p : TypedTuple colType → Bool) (a b : TypedRelation colType) :
    restriction p (intersection a b) = intersection (restriction p a) (restriction p b) := by
  sql_equiv

/-- `SELECT * FROM (a EXCEPT b) WHERE p ≡ (a WHERE p) EXCEPT (b WHERE p)`. -/
theorem select_diff (p : TypedTuple colType → Bool) (a b : TypedRelation colType) :
    restriction p (minus a b) = minus (restriction p a) (restriction p b) := by
  sql_equiv

/-- Applying the same `WHERE` twice is the same as once. -/
theorem select_idem (p : TypedTuple colType → Bool) (a : TypedRelation colType) :
    restriction p (restriction p a) = restriction p a := by
  sql_equiv

/-- `a UNION (a INTERSECT b) ≡ a` (absorption). -/
theorem union_absorb (a b : TypedRelation colType) :
    union a (intersection a b) = a := by
  sql_equiv

/-- Aggregation demo: a `LEFT JOIN`+`COALESCE(_,0)` count equals the correlated count. -/
theorem coalesce_count_demo {K : Type} [DecidableEq K]
    (key : TypedTuple colType → K) (k : K) (rel : TypedRelation colType) :
    (if k ∈ okeys key rel then cnt key k rel else 0) = cnt key k rel := by
  sql_equiv

end Example13
