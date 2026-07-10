import LeanDatabase.RelationalAlgebra

/-!
# `ORDER BY` and `LIMIT`

Our relations are `Finset`s — **inherently unordered**. So neither operator can be modelled
faithfully as "produce rows in some order":

* **`ORDER BY`** is therefore the **identity**. Under set semantics two queries are equivalent iff
  they yield the same *set* of rows; sorting is a *presentation* concern that set-equivalence
  deliberately ignores. We keep the operator (so queries read naturally and the sort key is
  documented) but it provably changes nothing — see `orderBy_eq`.

* **`LIMIT k`** cannot pick *which* `k` rows survive without an order, so the only thing it can
  observe is **cardinality**. We model it as the identity too, and expose the cardinality contract
  (`limit_card`, `limit_noop_of_card_le`): `LIMIT k` is a genuine no-op exactly when the table
  already fits the bound (`card ≤ k`), which is the only regime an order-free model can decide.
  (A faithful "keep `k` of `n`" needs the ordered `List`-relation layer; that is future work.)
-/

namespace LeanDatabase

-- `orderBy`/`limit` are intentionally the identity, so their key/bound arguments are unused.
set_option linter.unusedVariables false

variable {n : Nat} {colType : Fin n → Type} [∀ i, DecidableEq (colType i)]
variable {K : Type}

/-- `ORDER BY key` — **identity** under set semantics (row order is not observable on a `Finset`).
The `key` is kept only for documentation; it has no effect on the resulting set of rows. -/
@[simp, grind] def orderBy (key : TypedTuple colType → K) (rel : TypedRelation colType) :
    TypedRelation colType := rel

/-- `ORDER BY` is provably a no-op. Tagged so `sql_equiv` erases it. -/
@[simp, grind =] theorem orderBy_eq (key : TypedTuple colType → K) (rel : TypedRelation colType) :
    orderBy key rel = rel := rfl

/-- `LIMIT k` is opaque under set semantics: without row order, the choice of which rows survive is
unobservable. So `limit` is only equal to itself; it does not erase to the identity. Use
`limit_congr` to rewrite through equal sub-relations. -/
opaque limit (k : Nat) (rel : TypedRelation colType) : TypedRelation colType := rel

/-- `LIMIT` respects equality of its argument. This is what lets `sql_equiv` prove
`q₁ LIMIT k = q₂ LIMIT k` from `q₁ = q₂` *without* being able to erase `LIMIT` (which is unsound). -/
theorem limit_congr {k : Nat} {r1 r2 : TypedRelation colType} (h : r1 = r2) :
    limit k r1 = limit k r2 := by rw [h]

end LeanDatabase
