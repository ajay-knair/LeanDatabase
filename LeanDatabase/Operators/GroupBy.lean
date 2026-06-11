import LeanDatabase.Operators.Aggregate

/-!
# `GROUP BY` → relation, and `HAVING`

`groupByRel` produces one output row per distinct group key (`okeys`), built by `mkRow k rel`
(which computes the key columns + aggregates for group `k`, typically using `grp`/`cnt`/`sumI`/…).
`having` is a `WHERE` on the grouped relation.
-/

namespace LeanDatabase

open LeanDatabase.TypedAgg

variable {n p : Nat}
variable {colType : Fin n → Type} [∀ i, DecidableEq (colType i)]
variable {outCT : Fin p → Type} [∀ i, DecidableEq (outCT i)]
variable {K : Type} [DecidableEq K]

/-- `SELECT key, agg(...) FROM rel GROUP BY key` — one row per distinct key. -/
@[simp, grind] def groupByRel (key : TypedTuple colType → K) (newLabels : Fin p → String)
    (mkRow : K → TypedRelation colType → TypedTuple outCT) (rel : TypedRelation colType) :
    TypedRelation outCT :=
  { labels := newLabels, rows := (okeys key rel).image (fun k => mkRow k rel) }

/-- `HAVING p` — filter the grouped relation by an aggregate predicate. -/
@[simp, grind] def having (p : TypedTuple outCT → Bool) (grouped : TypedRelation outCT) :
    TypedRelation outCT :=
  restriction p grouped

/-- A `GROUP BY` produces at most one row per distinct group key. -/
theorem groupByRel_card_le (key : TypedTuple colType → K) (newLabels : Fin p → String)
    (mkRow : K → TypedRelation colType → TypedTuple outCT) (rel : TypedRelation colType) :
    (groupByRel key newLabels mkRow rel).rows.card ≤ (okeys key rel).card := by
  simp only [groupByRel]
  exact Finset.card_image_le

end LeanDatabase
