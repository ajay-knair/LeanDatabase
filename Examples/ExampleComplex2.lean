import LeanDatabase.Parser
import LeanDatabase.SQLSyntax
open LeanDatabase Lean

/-!
# Two more complex candidate equivalences

## Candidate 1 — predicate pushdown through a `JOIN` (left side)

```sql
SELECT * FROM (SELECT * FROM employees WHERE salary > 50000) AS e
  JOIN departments ON e.dept_id = departments.dept_id
  WHERE departments.budget > 100000
--- ≡ ---
SELECT * FROM employees JOIN departments ON employees.dept_id = departments.dept_id
  WHERE employees.salary > 50000 AND departments.budget > 100000
```

(`JOIN`'s right operand must be a bare table identifier in this parser's grammar, so only the left
side can be pushed into a subquery — the right side's filter stays in the outer `WHERE`.)

## Candidate 2 — `JOIN` distributes over `UNION` (on the left side)

```sql
SELECT * FROM (SELECT * FROM employees_east UNION SELECT * FROM employees_west) AS e
  JOIN departments ON e.dept_id = departments.dept_id
  WHERE departments.budget > 100000
--- ≡ ---
(SELECT * FROM employees_east JOIN departments ON employees_east.dept_id = departments.dept_id
   WHERE departments.budget > 100000)
UNION
(SELECT * FROM employees_west JOIN departments ON employees_west.dept_id = departments.dept_id
   WHERE departments.budget > 100000)
```
-/

namespace ExampleComplex2

CREATE TABLE employees (emp_id INT, dept_id INT, salary INT)
CREATE TABLE departments (dept_id INT, name STRING, budget INT)

theorem join_pushdown_left :
    sql%([employees_schema, departments_schema])
        "SELECT * FROM (SELECT * FROM employees WHERE salary > 50000) AS e JOIN departments ON dept_id = departments.dept_id WHERE departments.budget > 100000"
      = sql%([employees_schema, departments_schema])
        "SELECT * FROM employees JOIN departments ON employees.dept_id = departments.dept_id WHERE employees.salary > 50000 AND departments.budget > 100000" := by
  sql_equiv

end ExampleComplex2

namespace ExampleComplex2b

CREATE TABLE employees_east (emp_id INT, dept_id INT, salary INT)
CREATE TABLE employees_west (emp_id INT, dept_id INT, salary INT)
CREATE TABLE departments (dept_id INT, name STRING, budget INT)

theorem join_distrib_union :
    sql%([employees_east_schema, employees_west_schema, departments_schema])
        "SELECT * FROM (SELECT * FROM employees_east UNION SELECT * FROM employees_west) AS e JOIN departments ON dept_id = departments.dept_id WHERE departments.budget > 100000"
      = sql%([employees_east_schema, employees_west_schema, departments_schema])
        "SELECT * FROM employees_east JOIN departments ON employees_east.dept_id = departments.dept_id WHERE departments.budget > 100000 UNION SELECT * FROM employees_west JOIN departments ON employees_west.dept_id = departments.dept_id WHERE departments.budget > 100000" := by
  sql_equiv

end ExampleComplex2b
