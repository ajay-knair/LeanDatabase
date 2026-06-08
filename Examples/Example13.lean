import LeanDatabase.GrindToolbox
open LeanDatabase LeanDatabase.Aggregation

/-!
# Example 13

Multiple simple relational-algebra identities, plus two aggregate-over-`UNION ALL` identities.
-/

namespace Example13

/-! ## Set-semantics rewrites (`TypedRelation`) -/

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

/-! ## Bag-semantics aggregate over `UNION ALL` -/

structure Order where
  amount : Int
deriving DecidableEq, Repr

/-- `SUM(amount)` over a `UNION ALL` = sum of the parts. -/
theorem sum_unionAll (a b : List Order) :
    bagSum (·.amount) (a ++ b) = bagSum (·.amount) a + bagSum (·.amount) b := by
  grind +locals

/-- `COUNT(*)` over a `UNION ALL` = sum of the parts. -/
theorem count_unionAll (a b : List Order) :
    bagCount (a ++ b) = bagCount a + bagCount b := by
  grind +locals

end Example13
