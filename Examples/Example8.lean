import LeanDatabase.Parser
import LeanDatabase.SQLSyntax
open LeanDatabase Lean

/-!
# Example 8 — `NOT IN` ≡ `NOT EXISTS` (anti-join)

Keep the customers with no orders. The negative counterpart of Example 5; both are a
`restriction` of `customers` whose predicates agree by `TypedAgg.group_nonempty_iff`.
(NULL-free / dedup'd data, so the real-SQL `NOT IN` NULL pitfall does not arise.)

## The two SQL queries being proved equivalent

```sql
SELECT * FROM customers c WHERE c.customer_id NOT IN (SELECT customer_id FROM orders);
SELECT * FROM customers c WHERE NOT EXISTS (SELECT 1 FROM orders o WHERE o.customer_id = c.customer_id);
```
-/

namespace Example8

CREATE TABLE customers (customer_id INT, name STRING)
CREATE TABLE orders (customer_id INT, total INT)

-- The `antijoin` double-negation needs more search than the default budget.
set_option maxHeartbeats 1000000 in
theorem query_equivalence :
    sql%([customers_schema, orders_schema])
        "SELECT * FROM customers WHERE customers.customer_id NOT IN (SELECT orders.customer_id FROM orders)"
      = sql%([customers_schema, orders_schema])
        "SELECT * FROM customers WHERE NOT EXISTS (SELECT * FROM orders WHERE orders.customer_id = customers.customer_id)" := by
  sql_equiv

end Example8
