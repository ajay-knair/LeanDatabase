import LeanDatabase.Parser
import LeanDatabase.SQLSyntax
open LeanDatabase Lean

/-!
# Example 18 — `ORDER BY` + `LIMIT` + `LIKE`

Three of the order/pattern features at once. `WHERE name LIKE '%'`  keeps every row and ORDER BY is identity, so both sides reduce to LIMIT 10 R; they're equal because LIMIT is preserved by congruence (limit_congr) — not erased, since limit k R = R is deliberately unprovable.

```sql
SELECT * FROM R WHERE name LIKE '%' ORDER BY age LIMIT n   ≡   SELECT * FROM R
```
(`ORDER BY`/`LIMIT` only affect *presentation*/cardinality, which set-equivalence ignores; see
`orderBy_eq` / `limit_eq`.)
-/

namespace Example18

CREATE TABLE table (name STRING, age INT)

theorem query_equivalence :
    sql%([table_schema]) "SELECT * FROM table WHERE name LIKE \"%\" ORDER BY age LIMIT 10"
      = sql%([table_schema]) "SELECT * FROM table LIMIT 10" := by
  sql_equiv

end Example18
