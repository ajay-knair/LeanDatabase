import LeanDatabase.Parser
import LeanDatabase.SQLSyntax
open LeanDatabase Lean

/-!
# A more complicated equivalence, chaining four separate algebraic laws

`orders(order_id, region, amount, status)`.

Complex form: split by region into two `UNION`-ed branches, each independently filtered (one via
a double negation, the other directly) and cascaded through a nested subquery.

```sql
(SELECT * FROM (SELECT * FROM orders WHERE region = "US") AS a
   WHERE NOT (NOT (amount > 100)) AND status = "completed")
UNION
(SELECT * FROM (SELECT * FROM orders WHERE region = "EU") AS b
   WHERE amount > 100 AND status = "completed")
```

Flat form: one `WHERE` clause with the region check folded into a single `OR`.

```sql
SELECT * FROM orders WHERE (region = "US" OR region = "EU") AND amount > 100 AND status = "completed"
```

This chains four independently-proven laws into one equivalence: cascading `WHERE` ≡ `AND`
(Example2-style, `restriction_cascade`), double negation (Example0-style), `UNION` ≡ `OR` on
branches sharing a common conjunct (Example10-style, `restriction_pOr`), and `AND`
associativity/reordering.
-/

namespace ExampleComplex1

CREATE TABLE orders (order_id INT, region STRING, amount INT, status STRING)

theorem union_cascade_eq_or_and :
    sql%([orders_schema])
        "SELECT * FROM (SELECT * FROM orders WHERE region = \"US\") AS a WHERE NOT (NOT (amount > 100)) AND status = \"completed\" UNION SELECT * FROM (SELECT * FROM orders WHERE region = \"EU\") AS b WHERE amount > 100 AND status = \"completed\""
      = sql%([orders_schema])
        "SELECT * FROM orders WHERE (region = \"US\" OR region = \"EU\") AND amount > 100 AND status = \"completed\"" := by
  sql_equiv

end ExampleComplex1
