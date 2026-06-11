import LeanDatabase.SQLEquiv

open LeanDatabase

/-!
# Example 11 — "latest row per group", the four canonical SQL forms

The greatest-N-per-group pattern ("each customer's most recent order"). It is written four
canonical ways in the wild:

```sql
-- (1) ROW_NUMBER window function
SELECT * FROM (
  SELECT o.*, ROW_NUMBER() OVER (PARTITION BY customer_id ORDER BY created_at DESC) AS rn
  FROM orders o) x
WHERE x.rn = 1;

-- (2) self-join against a GROUP BY … MAX(…) subquery
SELECT o.* FROM orders o
JOIN (SELECT customer_id, MAX(created_at) AS latest FROM orders GROUP BY customer_id) m
  ON m.customer_id = o.customer_id AND m.latest = o.created_at;

-- (3) NOT EXISTS a strictly-later row
SELECT o.* FROM orders o
WHERE NOT EXISTS (SELECT 1 FROM orders o2
                  WHERE o2.customer_id = o.customer_id AND o2.created_at > o.created_at);

-- (4) LEFT JOIN self on a later row, keep where it IS NULL
SELECT o.* FROM orders o
LEFT JOIN orders o2
  ON o2.customer_id = o.customer_id AND o2.created_at > o.created_at
WHERE o2.customer_id IS NULL;
```

Forms **(2), (3), (4) are unconditionally equivalent** — each keeps exactly the rows whose
`created_at` is the group maximum (all of them, on ties). We model and prove these three below
with `sql_equiv`.

Form **(1) is the odd one out**: `ROW_NUMBER() = 1` returns exactly *one* row per group, breaking
ties arbitrarily — so it is *nondeterministic* under ties and coincides with (2)–(4) only when
`created_at` is unique within each customer group. We therefore document it but do not give it a
`TypedRelation` definition (a faithful model needs window/ordering machinery and a tie-break).
-/

namespace Example11

/-- `orders(customer_id : Nat, created_at : Nat)`. -/
abbrev ordCT : Fin 2 → Type := fun i => match i with | 0 => Nat | 1 => Nat
instance : ∀ i, DecidableEq (ordCT i) := fun i => match i with | 0 => inferInstance | 1 => inferInstance

abbrev ordKey : TypedTuple ordCT → Nat := fun t => t 0
abbrev createdAt : TypedTuple ordCT → Nat := fun t => t 1

/-- Form (2): `JOIN … MAX(created_at) … ON m.latest = o.created_at` — keep group-maximal rows. -/
@[simp] def query_MaxJoin (orders : TypedRelation ordCT) : TypedRelation ordCT :=
  restriction (fun o => decide (createdAt o = groupMaxN ordKey (ordKey o) orders createdAt)) orders

/-- Form (3): `WHERE NOT EXISTS (a strictly later row in the same group)`. -/
@[simp] def query_NotExistsLater (orders : TypedRelation ordCT) : TypedRelation ordCT :=
  restriction
    (fun o => decide (¬ ∃ s ∈ (grp ordKey (ordKey o) orders).rows, createdAt o < createdAt s)) orders

/-- Form (4): `LEFT JOIN` self on a later row, keep `WHERE later IS NULL` — i.e. the set of
    strictly-later rows in the group is empty. -/
@[simp] def query_LeftJoinNull (orders : TypedRelation ordCT) : TypedRelation ordCT :=
  restriction
    (fun o => decide (∀ s ∈ (grp ordKey (ordKey o) orders).rows, ¬ createdAt o < createdAt s)) orders

/-- `ROW_NUMBER() OVER (PARTITION BY customer_id ORDER BY created_at DESC)` for row `o`:
    one more than the number of strictly-later rows in `o`'s group. This is the *faithful* rank
    when `created_at` is unique within each group (the regime in which `ROW_NUMBER() = 1` is even
    deterministic); ties would need an extra tie-break column, which we assume away. -/
@[simp] def rnRank (orders : TypedRelation ordCT) (o : TypedTuple ordCT) : Nat :=
  1 + ((grp ordKey (ordKey o) orders).rows.filter (fun s => decide (createdAt o < createdAt s))).card

/-- Form (1): `… WHERE ROW_NUMBER() OVER (PARTITION BY customer_id ORDER BY created_at DESC) = 1`. -/
@[simp] def query_RowNumber (orders : TypedRelation ordCT) : TypedRelation ordCT :=
  restriction (fun o => decide (rnRank orders o = 1)) orders

/-- (1) ≡ (4): `ROW_NUMBER() = 1` keeps exactly the rows with no strictly-later row in their
    group — `rn = 1 ⇔ (#later rows) = 0 ⇔ the later-set is empty`. -/
theorem rowNumber_eq_leftJoinNull (orders : TypedRelation ordCT) :
    query_RowNumber orders = query_LeftJoinNull orders := by
  sql_equiv

/-- (2) ≡ (3): the `MAX` self-join equals the `NOT EXISTS`-a-later-row anti-join. -/
theorem maxJoin_eq_notExists (orders : TypedRelation ordCT) :
    query_MaxJoin orders = query_NotExistsLater orders := by
  sql_equiv

/-- (3) ≡ (4): `NOT EXISTS a later row` equals `LEFT JOIN … later IS NULL`. -/
theorem notExists_eq_leftJoinNull (orders : TypedRelation ordCT) :
    query_NotExistsLater orders = query_LeftJoinNull orders := by
  sql_equiv

/-- (2) ≡ (4): the `MAX` self-join equals the `LEFT JOIN … IS NULL` anti-join. -/
theorem maxJoin_eq_leftJoinNull (orders : TypedRelation ordCT) :
    query_MaxJoin orders = query_LeftJoinNull orders := by
  sql_equiv

end Example11
