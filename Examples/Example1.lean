import LeanDatabase.RelationalAlgebra

/-!
# Example 1 — Predicate pushdown through `UNION` (the "MapReduce" rewrite)

Distributivity of selection (`WHERE`) over union: filter-then-union equals union-then-filter.
A planner uses this to push a filter down to each branch so the branches can be scanned (and
filtered) independently / in parallel before being combined.

## The two SQL queries being proved equivalent

```sql
-- query_Slow: union everything first, then filter (one big pass)
SELECT * FROM (
  SELECT * FROM r1
  UNION
  SELECT * FROM r2
) WHERE is_high_value;

-- query_Fast: filter each branch first, then union (parallelizable)
SELECT * FROM r1 WHERE is_high_value
UNION
SELECT * FROM r2 WHERE is_high_value;
```
-/

namespace Example1
open LeanDatabase

variable {n : Nat}
variable {colType : Fin n → Type} [∀ i, DecidableEq (colType i)]
set_option linter.unusedSectionVars false

variable (isHighValue : TypedTuple colType → Bool)

/-- `SELECT * FROM (r1 UNION r2) WHERE is_high_value`. -/
def query_Slow (r1 r2 : TypedRelation colType) : TypedRelation colType :=
  restriction isHighValue (union r1 r2)

/-- `(SELECT * FROM r1 WHERE is_high_value) UNION (SELECT * FROM r2 WHERE is_high_value)`. -/
def query_Fast (r1 r2 : TypedRelation colType) : TypedRelation colType :=
  union (restriction isHighValue r1) (restriction isHighValue r2)

theorem query_equivalence (r1 r2 : TypedRelation colType) :
    query_Slow isHighValue r1 r2 = query_Fast isHighValue r1 r2 := by
  grind +locals

end Example1
