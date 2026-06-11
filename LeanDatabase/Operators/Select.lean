import LeanDatabase.RelationalAlgebra

/-!
# `SELECT`: computed projection and `DISTINCT`

`projection` (in `TypedRelation`) selects/reorders columns by index. `select` is the general
computed `SELECT list` — an arbitrary row transform `TypedTuple inCT → TypedTuple outCT`
(supports `SELECT a + b AS c`, constants, renames). `distinct` is `SELECT DISTINCT` — the
identity here, since the `Finset` model already carries no duplicates.
-/

namespace LeanDatabase

variable {n p : Nat}
variable {colType : Fin n → Type} [∀ i, DecidableEq (colType i)]
variable {outCT : Fin p → Type} [∀ i, DecidableEq (outCT i)]

/-- `SELECT <computed columns>`: map every row through `f`, de-duplicating (`Finset.image`). -/
@[simp, grind] def select (newLabels : Fin p → String)
    (f : TypedTuple colType → TypedTuple outCT) (rel : TypedRelation colType) : TypedRelation outCT :=
  { labels := newLabels, rows := rel.rows.image f }

/-- `SELECT DISTINCT *` — a syntactic marker for de-duplication. -/
def distinct (rel : TypedRelation colType) : TypedRelation colType := rel

/-- **`DISTINCT` is the identity** under set semantics: the `Finset` of rows already carries no
    duplicates, so removing them changes nothing. Tagged so `sql_simp`/`grind` erase `DISTINCT`. -/
@[simp, grind =] theorem distinct_eq (rel : TypedRelation colType) : distinct rel = rel := rfl

/-- A computed `SELECT` never produces more rows than the input. -/
theorem select_card_le (newLabels : Fin p → String)
    (f : TypedTuple colType → TypedTuple outCT) (rel : TypedRelation colType) :
    (select newLabels f rel).rows.card ≤ rel.rows.card := by
  simp only [select]
  exact Finset.card_image_le

/-- **`SELECT` composition**: two nested computed `SELECT`s fuse into one (image-of-image). -/
@[grind =] theorem select_compose {q : Nat} {finalCT : Fin q → Type} [∀ i, DecidableEq (finalCT i)]
    (l1 : Fin p → String) (l2 : Fin q → String)
    (f : TypedTuple colType → TypedTuple outCT) (g : TypedTuple outCT → TypedTuple finalCT)
    (rel : TypedRelation colType) :
    select l2 g (select l1 f rel) = select l2 (fun t => g (f t)) rel := by
  simp only [select, Finset.image_image, Function.comp_def]

/-- A computed `SELECT` over no rows produces no rows. -/
@[simp, grind =] theorem select_empty (newLabels : Fin p → String)
    (f : TypedTuple colType → TypedTuple outCT) (l : Fin n → String) :
    (select newLabels f (emptyRel (colType := colType) l)).rows = ∅ := by
  simp [select, emptyRel]

end LeanDatabase
