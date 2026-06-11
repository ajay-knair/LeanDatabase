import LeanDatabase.RelationalAlgebra

/-!
# `LIKE` — real wildcard pattern matching

`colContains` (in `Predicates`) only does substring search. `strLike` implements the genuine SQL
`LIKE` matcher over the two wildcards:

* `%` matches **any** (possibly empty) sequence of characters;
* `_` matches **exactly one** character;
* every other character matches itself literally.

`likeMatch` is the classic recursive backtracking matcher on `List Char` (the `%` case branches
on "consume a value char" vs. "finish the `%`"). `colLike proj pat` lifts it to a `WHERE`/`HAVING`
column predicate.
-/

namespace LeanDatabase

variable {n : Nat} {colType : Fin n → Type}

/-- Core `LIKE` matcher: does pattern `p` match value `v` (both as char lists)? -/
@[simp, grind .]
def likeMatch : List Char → List Char → Bool
  | [],        []      => true
  | [],        _ :: _  => false
  | '%' :: ps, []      => likeMatch ps []
  | '%' :: ps, c :: cs => likeMatch ('%' :: ps) cs || likeMatch ps (c :: cs)
  | '_' :: ps, _ :: cs => likeMatch ps cs
  | '_' :: _,  []      => false
  | p :: ps,   c :: cs => (p == c) && likeMatch ps cs
  | _ :: _,    []      => false
termination_by p v => p.length + v.length
decreasing_by all_goals grind

/-- String-level `LIKE`: `val LIKE pat`. -/
def strLike (pat val : String) : Bool := likeMatch pat.toList val.toList

/-- `col LIKE pat` as a `WHERE`/`HAVING` predicate (full `%`/`_` wildcard support). -/
@[simp, grind] def colLike (proj : TypedTuple colType → String) (pat : String) : TypedTuple colType → Bool :=
  fun t => strLike pat (proj t)

/-- The lone wildcard `%` matches every string. -/
@[simp] theorem likeMatch_pct (cs : List Char) : likeMatch ['%'] cs = true := by
  induction cs with
  | nil => grind only [likeMatch]
  | cons c cs ih => simp only [likeMatch, ih, Bool.true_or]

/-- `LIKE '%'` is satisfied by every string. Tagged so `sql_equiv` collapses `WHERE col LIKE '%'`. -/
@[simp] theorem strLike_pct (s : String) : strLike "%" s = true := by
  unfold strLike
  exact likeMatch_pct s.toList

end LeanDatabase
