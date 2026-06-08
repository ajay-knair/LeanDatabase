import LeanDatabase.TypedAggregation
open LeanDatabase LeanDatabase.TypedAgg

/-!
# Example 11 — "latest row per group": `MAX` self-join ≡ `NOT EXISTS` a-later-row

The greatest-N-per-group rewrite (the unconditionally-equivalent one; `ROW_NUMBER()=1` differs
on ties). On the `TypedRelation` algebra both queries are a `restriction` of `orders`: keep an
order iff its `created_at` is its group's `MAX(created_at)` (`TypedAgg.groupMaxN`), which by
`TypedAgg.eq_groupMaxN_iff` is the same as "no strictly later order of the same customer".

## The two SQL queries being proved equivalent

```sql
SELECT o.* FROM orders o
JOIN (SELECT customer_id, MAX(created_at) AS latest FROM orders GROUP BY customer_id) m
  ON m.customer_id = o.customer_id AND m.latest = o.created_at;

SELECT o.* FROM orders o
WHERE NOT EXISTS (SELECT 1 FROM orders o2
                  WHERE o2.customer_id = o.customer_id AND o2.created_at > o.created_at);
```
-/

namespace Example11

/-- `orders(customer_id : Nat, created_at : Nat)`. -/
abbrev ordCT : Fin 2 → Type := fun i => match i with | 0 => Nat | 1 => Nat
instance : ∀ i, DecidableEq (ordCT i) := fun i => match i with | 0 => inferInstance | 1 => inferInstance

abbrev ordKey : TypedTuple ordCT → Nat := fun t => t 0
abbrev createdAt : TypedTuple ordCT → Nat := fun t => t 1

/-- `JOIN … MAX(created_at) … ON m.latest = o.created_at`: keep group-maximal rows. -/
def query_MaxJoin (orders : TypedRelation ordCT) : TypedRelation ordCT :=
  restriction (fun o => decide (createdAt o = groupMaxN ordKey (ordKey o) orders createdAt)) orders

/-- `WHERE NOT EXISTS (… o2.customer_id = o.customer_id AND o2.created_at > o.created_at)`. -/
def query_NotExistsLater (orders : TypedRelation ordCT) : TypedRelation ordCT :=
  restriction
    (fun o => decide (¬ ∃ s ∈ (grp ordKey (ordKey o) orders).rows, createdAt o < createdAt s)) orders

theorem query_equivalence (orders : TypedRelation ordCT) :
    query_MaxJoin orders = query_NotExistsLater orders := by
  unfold query_MaxJoin query_NotExistsLater
  apply TypedRelation.ext
  · rfl
  · apply Finset.filter_congr
    intro o ho
    have hmem : o ∈ (grp ordKey (ordKey o) orders).rows := self_mem_grp ordKey orders o ho
    simp only [decide_eq_true_eq]
    rw [eq_groupMaxN_iff ordKey (ordKey o) orders createdAt o hmem]
    simp only [not_exists, not_and, Nat.not_lt]

end Example11
