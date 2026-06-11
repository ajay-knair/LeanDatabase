import LeanDatabase.RelationalAlgebra

/-!
# `WHERE`/`HAVING` predicate combinators

Boolean column predicates to build conditions compositionally. Combine with `pOr`/`pAnd`/`pNot`
(in `RelationalAlgebra`) for `AND`/`OR`/`NOT`. `proj : TypedTuple colType → α` picks the column.
-/

namespace LeanDatabase

variable {n : Nat} {colType : Fin n → Type}
variable {α : Type}

/-! These leaf predicates are tagged `@[simp]` so they unfold to their `decide (…)` form, which
`grind` reasons about natively. That keeps them **transparent to automation**: an autoconverter can
emit `colEq`/`colLt`/`between`/`inList` directly (no raw `decide`) and `sql_equiv` still discharges
goals that need the predicate's *meaning* (contradictions, concrete `IN`-lists, value comparisons).
The compound combinators `pOr`/`pAnd`/`pNot` stay opaque (see `RelationalAlgebra`). -/

/-- `col = v`. -/
@[simp] def colEq [DecidableEq α] (proj : TypedTuple colType → α) (v : α) : TypedTuple colType → Bool :=
  fun t => decide (proj t = v)

/-- `col <> v`. -/
@[simp] def colNe [DecidableEq α] (proj : TypedTuple colType → α) (v : α) : TypedTuple colType → Bool :=
  fun t => decide (proj t ≠ v)

/-- `col < v`. -/
@[simp] def colLt [LinearOrder α] (proj : TypedTuple colType → α) (v : α) : TypedTuple colType → Bool :=
  fun t => decide (proj t < v)

/-- `col <= v`. -/
@[simp] def colLe [LinearOrder α] (proj : TypedTuple colType → α) (v : α) : TypedTuple colType → Bool :=
  fun t => decide (proj t ≤ v)

/-- `col > v`. -/
@[simp] def colGt [LinearOrder α] (proj : TypedTuple colType → α) (v : α) : TypedTuple colType → Bool :=
  fun t => decide (v < proj t)

/-- `col >= v`. -/
@[simp] def colGe [LinearOrder α] (proj : TypedTuple colType → α) (v : α) : TypedTuple colType → Bool :=
  fun t => decide (v ≤ proj t)

/-- `col BETWEEN lo AND hi` (inclusive). -/
@[simp] def between [LinearOrder α] (proj : TypedTuple colType → α) (lo hi : α) : TypedTuple colType → Bool :=
  fun t => decide (lo ≤ proj t ∧ proj t ≤ hi)

/-- `col IN (v₁, …, vₖ)`. -/
@[simp] def inList [DecidableEq α] (proj : TypedTuple colType → α) (vs : List α) : TypedTuple colType → Bool :=
  fun t => decide (proj t ∈ vs)

/-- `col LIKE '%pat%'` — substring match (the common wildcard case). -/
def colContains (proj : TypedTuple colType → String) (pat : String) : TypedTuple colType → Bool :=
  fun t => (proj t).splitOn pat |>.length |> (· > 1) |> (fun b => b || pat.isEmpty)

/-! ## Predicate-algebra rewrites

These relate the combinators to each other (negation duality, `BETWEEN` desugaring, `IN`
cons/nil). They are tagged `@[grind =]` only — NOT `@[simp]` — so the combinator shape survives
`sql_simp`'s normalization (keeping LHSs first-order/e-matchable), and grind can use them to close
the per-row `Bool` goals left by `Finset.filter_congr`. -/

/-- `col <> v` is the negation of `col = v`. -/
@[grind =] theorem colNe_eq_not_colEq [DecidableEq α] (proj : TypedTuple colType → α) (v : α) :
    colNe proj v = fun t => !colEq proj v t := by
  funext t; simp only [colNe, colEq, ne_eq, decide_not]

/-- `col >= v` is the negation of `col < v`. -/
@[grind =] theorem colGe_eq_not_colLt [LinearOrder α] (proj : TypedTuple colType → α) (v : α) :
    colGe proj v = fun t => !colLt proj v t := by
  funext t; simp only [colGe, colLt, ← not_lt, decide_not]

/-- `col <= v` is the negation of `col > v`. -/
@[grind =] theorem colLe_eq_not_colGt [LinearOrder α] (proj : TypedTuple colType → α) (v : α) :
    colLe proj v = fun t => !colGt proj v t := by
  funext t; simp only [colLe, colGt, ← not_lt, decide_not]

/-- `col BETWEEN lo AND hi` desugars to `col >= lo AND col <= hi`. -/
@[grind =] theorem between_eq_and [LinearOrder α] (proj : TypedTuple colType → α) (lo hi : α) :
    between proj lo hi = fun t => colGe proj lo t && colLe proj hi t := by
  funext t; simp only [between, colGe, colLe]; grind

/-- `col IN ()` is always false. -/
@[simp, grind =] theorem inList_nil [DecidableEq α] (proj : TypedTuple colType → α) :
    inList proj [] = fun _ => false := by
  funext t; simp only [inList, List.not_mem_nil, decide_false]

/-- `col IN (v, vs…)` unfolds to `col = v OR col IN (vs…)`. -/
@[grind =] theorem inList_cons [DecidableEq α] (proj : TypedTuple colType → α) (v : α) (vs : List α) :
    inList proj (v :: vs) = fun t => colEq proj v t || inList proj vs t := by
  funext t; simp only [inList, colEq, List.mem_cons]; grind

end LeanDatabase
