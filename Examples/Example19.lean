import LeanDatabase.SQLEquiv
open LeanDatabase

/-!
# Example 19 — `NULL` handling and `LEFT OUTER JOIN`

Two facts about the nullable layer:

1. **`NOT NULL` after lifting** — a freshly lifted table has no `NULL`s, so `WHERE col IS NULL`
   returns nothing.
2. **`LEFT JOIN` against an empty table** — no right row can match, so every left row survives,
   padded with `NULL`s on the right columns (i.e. it degenerates to `R × {NULL…}`):

```sql
SELECT * FROM R LEFT JOIN S ON R.a = S.a   -- with S empty
≡  SELECT R.*, NULL AS …  FROM R
```
-/

namespace Example19

abbrev rCT : Fin 1 → Type := fun _ => Nat
abbrev sCT : Fin 1 → Type := fun _ => Nat
instance : ∀ i, DecidableEq (rCT i) := fun _ => inferInstance
instance : ∀ i, DecidableEq (sCT i) := fun _ => inferInstance
instance : ∀ i, Inhabited (rCT i) := fun _ => inferInstance
instance : ∀ i, Inhabited (sCT i) := fun _ => inferInstance

/-- `EXISTS`/join condition `R.a = S.a`. -/
abbrev cond (r : TypedTuple rCT) (s : TypedTuple sCT) : Bool := decide (r 0 = s 0)

/-- **NULL handling**: lifting a `NOT NULL` table introduces no `NULL`s. -/
theorem no_nulls_after_lift (R : TypedRelation rCT) :
    (restriction (isNull (fun t => t 0)) (liftNullable R)).rows = ∅ := by
  sql_equiv

/-- **LEFT OUTER JOIN** with an empty right table: all left rows survive, `NULL`-padded. -/
theorem leftJoin_empty_right (R : TypedRelation rCT) (l2 : Fin 1 → String) :
    (leftOuterJoin R (emptyRel l2) cond).rows = (crossProductRel R (nullRow sCT l2)).rows := by
  sql_equiv

end Example19
