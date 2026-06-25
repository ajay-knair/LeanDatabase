import LeanDatabase.Parser
import LeanDatabase.SQLSyntax
open LeanDatabase Lean

/-!
# Example 5 — `EXISTS` correlated subquery ≡ `IN` subquery (semi-join)

Keep the customers that have at least one order. On the `TypedRelation` algebra: both queries
are a `restriction` of `customers`; the predicates agree by `TypedAgg.group_nonempty_iff`
("a customer's order group is non-empty iff its id occurs among order keys").

## The two SQL queries being proved equivalent

```sql
SELECT * FROM customers c WHERE EXISTS (SELECT 1 FROM orders o WHERE o.customer_id = c.customer_id);
SELECT * FROM customers c WHERE c.customer_id IN (SELECT customer_id FROM orders);
```
-/

namespace Example5

CREATE TABLE customers (customer_id INT, name STRING)
CREATE TABLE orders (customer_id INT, total INT)

theorem query_equivalence :
    sql%([customers_schema, orders_schema])
        "SELECT * FROM customers WHERE EXISTS (SELECT * FROM orders WHERE orders.customer_id = customers.customer_id)"
      = sql%([customers_schema, orders_schema])
        "SELECT * FROM customers WHERE customers.customer_id IN (SELECT orders.customer_id FROM orders)" := by
  sql_equiv

end Example5
