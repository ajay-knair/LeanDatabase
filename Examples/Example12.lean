import LeanDatabase.Parser
import LeanDatabase.SQLSyntax
open LeanDatabase Lean LeanDatabase.TypedAgg

/-!
# Example 12 — `SUM(CASE…)` + `HAVING` ≡ `WHERE` + `SUM` + `HAVING`

Filtering inside the aggregate with `CASE` equals filtering rows with `WHERE` before
aggregating — so the planner may push `status = 'completed'` into a `WHERE`.

## The two SQL queries being proved equivalent

```sql
SELECT customer_id,
       SUM(CASE WHEN status = 'completed' THEN total_amount ELSE 0 END) AS completed_total
FROM orders GROUP BY customer_id
HAVING SUM(CASE WHEN status = 'completed' THEN total_amount ELSE 0 END) > 1000;
                                  ≡
SELECT customer_id, SUM(total_amount) AS completed_total
FROM orders WHERE status = 'completed' GROUP BY customer_id
HAVING SUM(total_amount) > 1000;
```

The two `GROUP BY`s scan *different* base relations (all orders vs. the completed ones), so beyond the
per-group `SUM(CASE)`≡`WHERE`+`SUM` value identity (`groupSum_caseProp_eq_groupSum_where`) the proof
also matches their output key-sets: a customer survives `HAVING SUM > 1000` only if it has a completed
order (`mem_groupKeys_of_groupSum_ne_zero`), which is exactly `image_where_absorb`.
-/

namespace Example12

CREATE TABLE orders (customer_id INT, status STRING, total_amount INT)

theorem query_equivalence :
    sql%([orders_schema])
        "SELECT customer_id, SUM(CASE WHEN status = \"completed\" THEN total_amount ELSE 0 END) AS completed_total FROM orders GROUP BY customer_id HAVING SUM(CASE WHEN status = \"completed\" THEN total_amount ELSE 0 END) > 1000"
      = sql%([orders_schema])
        "SELECT customer_id, SUM(total_amount) AS completed_total FROM orders WHERE status = \"completed\" GROUP BY customer_id HAVING SUM(total_amount) > 1000" := by
  funext orders
  -- fold each `SUM(CASE)` into the matching `WHERE`-restricted `SUM`; now both sides share the same
  -- per-key output and `HAVING`, differing only in whether the base was `WHERE`-restricted.
  simp only [TypedRelation.mapByList, groupSum_case_eq_groupSum_where]
  apply TypedRelation.ext (by rfl)
  apply image_where_absorb (key := fun t => t 0)
  case hpres =>
    -- a customer passing `HAVING SUM(total_amount) > 1000` has a completed order, so its key survives
    intro t _ hgt
    simp only [mem_groupKeys]
    have h2 := mem_groupKeys_of_groupSum_ne_zero
      (fun tt : TypedTupleOfList [SQLTypeProxy.int, SQLTypeProxy.string, SQLTypeProxy.int] =>
        TypedTupleOfList.cons SQLTypeProxy.int (tt 0) TypedTupleOfList.nil)
      (TypedTupleOfList.cons SQLTypeProxy.int (t 0) TypedTupleOfList.nil) _ (fun tt => tt 2)
      (fun hz => by rw [hz] at hgt; simp at hgt)
    rw [mem_groupKeys] at h2
    obtain ⟨s, hs, hks⟩ := h2
    refine ⟨s, hs, ?_⟩
    have h0 := congrFun hks (0 : Fin 1)
    simp only [TypedTupleOfList.cons] at h0
    exact h0
  -- the per-key output `mk` and the `HAVING` predicate both factor through the group key
  all_goals sql_equiv

end Example12
