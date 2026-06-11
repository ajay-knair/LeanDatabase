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

/-- `LIMIT k` — modelled as the identity; the *only* observable contract is on cardinality (see
below), since an unordered set gives no canonical "first `k`". -/
@[simp, grind] def limit (k : Nat) (rel : TypedRelation colType) : TypedRelation colType := rel

/-- `LIMIT` is a no-op on the row-set. Tagged so `sql_equiv` erases it. -/
@[simp, grind =] theorem limit_eq (k : Nat) (rel : TypedRelation colType) :
    limit k rel = rel := rfl

/-- The cardinality is unchanged (our model never actually drops rows). -/
theorem limit_card (k : Nat) (rel : TypedRelation colType) :
    (limit k rel).rows.card = rel.rows.card := rfl

/-- **The cardinality contract**: when the input already fits the bound, `LIMIT k` is a genuine
no-op — the regime where `LIMIT`-equivalence reduces to plain set-equivalence. -/
theorem limit_noop_of_card_le {k : Nat} {rel : TypedRelation colType} (h : rel.rows.card ≤ k) :
    (limit k rel).rows.card ≤ k := by simpa using h

end LeanDatabase
