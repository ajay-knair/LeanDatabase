import LeanDatabase.Parser
import LeanDatabase.SQLSyntax
open LeanDatabase Lean

/-!
# Example 18 — `ORDER BY` + `LIMIT` + `LIKE`

Three of the order/pattern features at once. `WHERE name LIKE '%'` keeps every row (the lone `%`
matches anything), and under set semantics `ORDER BY` and `LIMIT` are no-ops on the row-set — so
the whole query collapses to `R`:

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
      = sql%([table_schema]) "SELECT * FROM table" := by
  sql_equiv

end Example18
