import LeanDatabase.Parser
import LeanDatabase.SQLSyntax
open LeanDatabase Lean

/-!
# Example 4 — Combine + global anti-set ≡ single combined predicate

Take active users from two tables, then remove anyone in the global banned set; this equals
unioning the two tables and keeping rows that are active and not banned in one pass.

## The two SQL queries being proved equivalent

```sql
-- query_Messy: (active(A) ∪ active(B)) minus banned(A ∪ B)
(SELECT * FROM tableA WHERE is_active
 UNION
 SELECT * FROM tableB WHERE is_active)
EXCEPT
SELECT * FROM (SELECT * FROM tableA UNION SELECT * FROM tableB) WHERE is_banned;

-- query_Clean: union first, then one combined predicate
SELECT * FROM (SELECT * FROM tableA UNION SELECT * FROM tableB)
WHERE is_active AND NOT is_banned;
```
-/

namespace Example4

CREATE TABLE tableA (is_active BOOL, is_banned BOOL)
CREATE TABLE tableB (is_active BOOL, is_banned BOOL)

theorem query_equivalence :
    sql%([tableA_schema, tableB_schema])
        "(SELECT * FROM tableA WHERE tableA.is_active UNION SELECT * FROM tableB WHERE tableB.is_active) EXCEPT SELECT * FROM (SELECT * FROM tableA UNION SELECT * FROM tableB) AS u WHERE is_banned"
      = sql%([tableA_schema, tableB_schema])
        "SELECT * FROM (SELECT * FROM tableA UNION SELECT * FROM tableB) AS u WHERE is_active AND NOT is_banned" := by
  sql_equiv

end Example4
