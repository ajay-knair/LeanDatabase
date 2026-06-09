import LeanDatabase.RelationalAlgebra

/-!
# Example 2 — Cascading selection (the "Index Merge" rewrite)

Two `WHERE` filters applied one after another equal a single filter testing both conditions
at once. A planner uses this to collapse a multi-pass scan into one pass (or a single
composite index seek).

## The two SQL queries being proved equivalent

```sql
-- query_MultiPass: filter for active, then filter that result for high value (two passes)
SELECT * FROM (
  SELECT * FROM r WHERE is_active
) WHERE is_high_value;

-- query_SinglePass: test both conditions in one pass
SELECT * FROM r WHERE is_high_value AND is_active;
```
-/

namespace Example2
open LeanDatabase

variable {n : Nat}
variable {colType : Fin n → Type} [∀ i, DecidableEq (colType i)]
set_option linter.unusedSectionVars false

variable (isHighValue : TypedTuple colType → Bool)
variable (isActive : TypedTuple colType → Bool)

/-- `SELECT * FROM (SELECT * FROM r WHERE is_active) WHERE is_high_value`. -/
def query_MultiPass (r : TypedRelation colType) : TypedRelation colType :=
  restriction isHighValue (restriction isActive r)

/-- `SELECT * FROM r WHERE is_high_value AND is_active`. -/
def query_SinglePass (r : TypedRelation colType) : TypedRelation colType :=
  restriction (fun t => isHighValue t && isActive t) r

theorem query_equivalence (r : TypedRelation colType) :
    query_MultiPass isHighValue isActive r = query_SinglePass isHighValue isActive r := by
  sorry
  --grind +locals

end Example2
