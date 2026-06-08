import LeanDatabase.GrindToolbox
open LeanDatabase LeanDatabase.TypedAgg

/-!
# Example 13 — toolbox demo: equivalences that close "for free"

Each equivalence below needs a lemma that isn't specific to the example — they live in
`LeanDatabase.GrindToolbox` (set-algebra rewrites) and `LeanDatabase.TypedAggregation`
(aggregation/coalesce). Importing the toolbox lets every query equivalence here close with a
bare `grind +locals`, on the `TypedRelation` algebra.
-/

namespace Example13

variable {n : Nat} {colType : Fin n → Type} [∀ i, DecidableEq (colType i)]
set_option linter.unusedSectionVars false

/-- `SELECT * FROM (a INTERSECT b) WHERE p ≡ (a WHERE p) INTERSECT (b WHERE p)`. -/
theorem select_inter (p : TypedTuple colType → Bool) (a b : TypedRelation colType) :
    restriction p (intersection a b) = intersection (restriction p a) (restriction p b) := by
  grind +locals

/-- `SELECT * FROM (a EXCEPT b) WHERE p ≡ (a WHERE p) EXCEPT (b WHERE p)`. -/
theorem select_diff (p : TypedTuple colType → Bool) (a b : TypedRelation colType) :
    restriction p (minus a b) = minus (restriction p a) (restriction p b) := by
  grind +locals

/-- Applying the same `WHERE` twice is the same as once. -/
theorem select_idem (p : TypedTuple colType → Bool) (a : TypedRelation colType) :
    restriction p (restriction p a) = restriction p a := by
  grind +locals

/-- `a UNION (a INTERSECT b) ≡ a` (absorption). -/
theorem union_absorb (a b : TypedRelation colType) :
    union a (intersection a b) = a := by
  grind +locals

/-- Aggregation demo: a `LEFT JOIN`+`COALESCE(_,0)` count equals the correlated count. -/
theorem coalesce_count_demo {K : Type} [DecidableEq K]
    (key : TypedTuple colType → K) (k : K) (rel : TypedRelation colType) :
    (if k ∈ okeys key rel then cnt key k rel else 0) = cnt key k rel := by
  grind +locals

end Example13
