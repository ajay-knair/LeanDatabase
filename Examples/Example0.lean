import LeanDatabase.Parser
import LeanDatabase.SQLSyntax
open LeanDatabase Lean

/-!
# Example 0 — Ten equivalences on raw SQL, with `CREATE TABLE` schemas

Tables are declared with `CREATE TABLE` (`SQLSyntax.lean`), which emits `<t>_schema`. Each theorem
states two SQL queries as plain text via `sql%([<t>_schema, …]) "…"` (`Parser.lean`), and `sql_equiv`
proves them equal — exercising the whole pipeline (DDL → parser → algebra → tactic).
-/

namespace Example0

CREATE TABLE table (age INT, isActive BOOL, height FLOAT)
CREATE TABLE table2 (age INT, isActive BOOL)

/-! ## 1. `WHERE` conjuncts may be reordered -/
theorem and_reorder :
    sql%([table_schema]) "SELECT * FROM table WHERE age > 30 AND isActive"
      = sql%([table_schema]) "SELECT * FROM table WHERE isActive AND age > 30" := by
  sql_equiv

/-! ## 2. A repeated conjunct is idempotent -/
theorem and_idempotent :
    sql%([table_schema]) "SELECT * FROM table WHERE isActive AND isActive"
      = sql%([table_schema]) "SELECT * FROM table WHERE isActive" := by
  sql_equiv

/-! ## 3. Two comparison filters commute -/
theorem cmp_reorder :
    sql%([table_schema]) "SELECT * FROM table WHERE age > 30 AND height < 180"
      = sql%([table_schema]) "SELECT * FROM table WHERE height < 180 AND age > 30" := by
  sql_equiv

/-! ## 4. Double negation -/
theorem double_negation :
    sql%([table_schema]) "SELECT * FROM table WHERE NOT (NOT isActive)"
      = sql%([table_schema]) "SELECT * FROM table WHERE isActive" := by
  sql_equiv

/-! ## 5. De Morgan -/
theorem de_morgan :
    sql%([table_schema]) "SELECT * FROM table WHERE NOT (age > 30 OR isActive)"
      = sql%([table_schema]) "SELECT * FROM table WHERE NOT (age > 30) AND NOT isActive" := by
  sql_equiv

/-! ## 6. `OR` is idempotent -/
theorem or_idempotent :
    sql%([table_schema]) "SELECT * FROM table WHERE isActive OR isActive"
      = sql%([table_schema]) "SELECT * FROM table WHERE isActive" := by
  sql_equiv

/-! ## 7. A repeated comparison is redundant -/
theorem cmp_redundant :
    sql%([table_schema]) "SELECT * FROM table WHERE age > 30 AND age > 30"
      = sql%([table_schema]) "SELECT * FROM table WHERE age > 30" := by
  sql_equiv

/-! ## 8. Absorption: `p OR (p AND q)` simplifies to `p` -/
theorem absorption :
    sql%([table_schema]) "SELECT * FROM table WHERE isActive OR (isActive AND age > 30)"
      = sql%([table_schema]) "SELECT * FROM table WHERE isActive" := by
  sql_equiv

/-! ## 9. Comma-product filter conjuncts commute (two tables) -/
theorem join_where_reorder :
    sql%([table_schema, table2_schema])
        "SELECT * FROM table, table2 WHERE table.age = table2.age AND table.isActive"
      = sql%([table_schema, table2_schema])
        "SELECT * FROM table, table2 WHERE table.isActive AND table.age = table2.age" := by
  sql_equiv

/-! ## 10. `JOIN … ON` is the comma-product plus the `ON` condition in `WHERE` -/
theorem join_is_comma_where :
    sql%([table_schema, table2_schema]) "SELECT * FROM table JOIN table2 ON table.age = table2.age"
      = sql%([table_schema, table2_schema]) "SELECT * FROM table, table2 WHERE table.age = table2.age" := by
  sql_equiv

end Example0
