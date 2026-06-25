import LeanDatabase.Parser
import LeanDatabase.SQLSyntax
open LeanDatabase Lean

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

CREATE TABLE r1 (is_high_value BOOL, val INT)
CREATE TABLE r2 (is_high_value BOOL, val INT)

theorem query_equivalence :
    sql%([r1_schema, r2_schema])
        "SELECT * FROM (SELECT * FROM r1 UNION SELECT * FROM r2) AS u WHERE is_high_value"
      = sql%([r1_schema, r2_schema])
        "SELECT * FROM r1 WHERE r1.is_high_value UNION SELECT * FROM r2 WHERE r2.is_high_value" := by
  sql_equiv

end Example1
