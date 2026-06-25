import LeanDatabase.Parser
import LeanDatabase.SQLSyntax
open LeanDatabase Lean

/-!
# Example 16 — `SELECT f DISTINCT (WHERE q (WHERE p))` ≡ `SELECT f (WHERE p AND q)`

Combines computed `SELECT` (`select`), `DISTINCT` (a no-op on a set), and cascaded `WHERE`
(two filters collapse to one `AND`).

```sql
SELECT DISTINCT g(R) FROM (SELECT * FROM (SELECT * FROM R WHERE q) WHERE p)
≡  SELECT g(R) FROM R WHERE p AND q
```
-/

namespace Example16

-- `g(R) = a + b`; `p`, `q` are the `WHERE` predicates (modelled as `BOOL` columns).
CREATE TABLE R (a INT, b INT, p BOOL, q BOOL)

theorem query_equivalence :
    sql%([R_schema])
        "SELECT DISTINCT a + b AS g FROM (SELECT * FROM (SELECT * FROM R WHERE q) AS x WHERE p) AS y"
      = sql%([R_schema]) "SELECT a + b AS g FROM R WHERE p AND q" := by
  sql_equiv

end Example16
