import LeanDatabase.Parser
import LeanDatabase.SQLSyntax
open LeanDatabase Lean

/-!
# Example 10 — `OR` predicate ≡ `UNION` ≡ disjoint `UNION ALL`

Three ways to write "tickets that are open or high priority", all equivalent. This is a
*set-semantics* fact: `UNION` deduplicates, and `OR` over a set returns each matching row
once — so we model it with the `Finset`-based `TypedRelation` (not bags). The third form makes
the two branches disjoint (`priority='high' AND status<>'open'`) so even `UNION ALL` produces
no duplicates.

## The three SQL queries being proved equivalent

```sql
-- query_Or:
SELECT * FROM tickets WHERE status = 'open' OR priority = 'high';

-- query_Union:
SELECT * FROM tickets WHERE status = 'open'
UNION
SELECT * FROM tickets WHERE priority = 'high';

-- query_UnionAll: branches made disjoint, so UNION ALL is safe
SELECT * FROM tickets WHERE status = 'open'
UNION ALL
SELECT * FROM tickets WHERE priority = 'high' AND status <> 'open';
```
-/

namespace Example10

CREATE TABLE table (status STRING, priority STRING)

/-- `query_Or` ≡ `query_Union`. -/
theorem or_eq_union :
    sql%([table_schema]) "SELECT * FROM table WHERE status = \"open\" OR priority = \"high\""
      = sql%([table_schema])
          "SELECT * FROM table WHERE status = \"open\" UNION SELECT * FROM table WHERE priority = \"high\"" := by
  sql_equiv

/-- `query_Or` ≡ `query_UnionAll` (disjoint branches). -/
theorem or_eq_union_all :
    sql%([table_schema]) "SELECT * FROM table WHERE status = \"open\" OR priority = \"high\""
      = sql%([table_schema])
          "SELECT * FROM table WHERE status = \"open\" UNION ALL SELECT * FROM table WHERE priority = \"high\" AND status <> \"open\"" := by
  sql_equiv

end Example10
