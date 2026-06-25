import Lean
open Lean
/-!
# SQL surface syntax

The `sql_query` / `sql_from` / `sql_cols` / `sql_col` syntax categories, the `macro_rules` that
desugar `JOIN` / `CROSS JOIN` into comma-separated cartesian products, and the term-level
`AND` / `OR` / `NOT` combinators that let `WHERE` predicates be written SQL-style.

Pure syntax: depends only on `Lean`, not on the type layer (`Parser.Types`). The two are joined in
`Parser.Query`.
-/

open Lean

namespace LeanDatabase

declare_syntax_cat sql_query
declare_syntax_cat sql_from
declare_syntax_cat sql_cols
syntax "*" : sql_cols
declare_syntax_cat sql_col
syntax ident : sql_col
syntax term "AS" ident : sql_col
syntax sql_col,* : sql_cols

def sqlColTerm : TSyntax `sql_col → Syntax.Term
  | `(sql_col| $col:ident) => col
  | `(sql_col| $col:term AS $_:ident) => col
  | _ => unreachable!

def sqlColName : TSyntax `sql_col → Name
  | `(sql_col| $col:ident) => col.getId
  | `(sql_col| $_:term AS $x:ident) => x.getId
  | _ => unreachable!

-- Base Cases (The atomic sources of data)
syntax ident : sql_from                               -- 1. Standard table name
syntax "(" sql_query ")" "AS" ident : sql_from       -- 2. Subquery with mandatory alias

-- Recursive Cases (Chaining joins from left to right)
syntax sql_from "JOIN" ident "ON" term : sql_from     -- 3. Explicit Inner Join
syntax sql_from "CROSS" "JOIN" ident : sql_from       -- 4. Cross Join
syntax sql_from "," sql_from : sql_from              -- 5. Comma-separated (Cartesian Product)

syntax "SELECT " (" DISTINCT ")? sql_cols " FROM " sql_from (" WHERE " term)?  (" GROUP " " BY " ident,* (" HAVING " term)?)? (" ORDER " " BY " sql_col,*)? (" LIMIT " num)? (";")? : sql_query

-- Binary set operators on whole queries, as one keyword-parameterised production. Our relations
-- are `Finset`s (sets), so `UNION ALL` maps to set `union` too (no bag semantics).
declare_syntax_cat sql_setop
syntax " UNION " " ALL " : sql_setop
syntax " UNION " : sql_setop
syntax " INTERSECT " : sql_setop
syntax " EXCEPT " : sql_setop
syntax:40 sql_query:40 sql_setop sql_query:41 : sql_query

-- Parenthesised query, for grouping set-ops: `a UNION (a INTERSECT b)`.
syntax:max "(" sql_query ")" : sql_query

-- macro_rules -- Gemini generated (then fixed) rules for desugaring JOINs and CROSS JOINs into comma-separated FROM clauses with WHERE conditions; GROUP BY omitted for now.
--   -----------------------------------------------------------------------------
--   -- CASE A: The query ALREADY has an existing WHERE clause
--   -----------------------------------------------------------------------------
--   -- 1. Desugar INNER JOIN -> Replace with comma, append condition via AND

--   | `(sql_query| SELECT $items FROM $f:sql_from JOIN $tNext:ident ON $onCond WHERE $whereCond $[;]?) =>
--       `(sql_query| SELECT $items FROM $f, $tNext:ident WHERE $whereCond AND $onCond;)

--   -- 2. Desugar CROSS JOIN -> Replace with comma, leave WHERE unchanged

--   | `(sql_query| SELECT $items FROM $f:sql_from CROSS JOIN $tNext:ident WHERE $whereCond $[;]?) =>
--       `(sql_query| SELECT $items FROM $f, $tNext:ident WHERE $whereCond ;)

--   -----------------------------------------------------------------------------
--   -- CASE B: The query does NOT have a WHERE clause yet
--   -----------------------------------------------------------------------------
--   -- 3. Desugar INNER JOIN -> Initialize the WHERE clause with the ON condition

--   | `(sql_query| SELECT $items FROM $f:sql_from JOIN $tNext:ident ON $onCond:term $[;]?) =>
--       `(sql_query| SELECT $items FROM $f, $tNext:ident WHERE $onCond ;)

--   -- 4. Desugar CROSS JOIN -> Replace with comma, no WHERE clause needed

--   | `(sql_query| SELECT $items FROM $f:sql_from CROSS JOIN $tNext:ident $[;]?) =>
--       `(sql_query| SELECT $items FROM $f, $tNext:ident;)

partial def escapeJoin (stx : Syntax) : MetaM <| TSyntax `sql_query := do
  match stx with
  | `(sql_query| SELECT $items FROM $f:sql_from JOIN $tNext:ident ON $onCond:term WHERE $whereCond $[;]?) =>
      escapeJoin <| ← `(sql_query| SELECT $items FROM $f, $tNext:ident WHERE $whereCond && $onCond;)
  | `(sql_query| SELECT $items FROM $f:sql_from CROSS JOIN $tNext:ident WHERE $whereCond $[;]?) =>
      escapeJoin <| ← `(sql_query| SELECT $items FROM $f, $tNext:ident WHERE $whereCond ;)
  | `(sql_query| SELECT $items FROM $f:sql_from JOIN $tNext:ident ON $onCond:term $[;]?) =>
      escapeJoin <| ← `(sql_query| SELECT $items FROM $f, $tNext:ident WHERE $onCond ;)
  | `(sql_query| SELECT $items FROM $f:sql_from CROSS JOIN $tNext:ident $[;]?) =>
      escapeJoin <| ← `(sql_query| SELECT $items FROM $f, $tNext:ident;)
  | _ => return ⟨stx⟩

partial def getIdents (stx : TSyntax `sql_from) : List Name :=
  match stx with
  | `(sql_from| $db:ident) => [db.getId]
  | `(sql_from| $f1:sql_from , $f2:sql_from) => getIdents f1 ++ getIdents f2
  | _ => []

/-! ## Term-level `WHERE`-predicate combinators -/

-- macro "SELECT" " * " "FROM" ident "WHERE" t:term : term =>
--     return t

macro:30 t:term "AND" s:term : term =>
  `($t && $s)

macro:30 t:term "OR" s:term : term =>
  `($t || $s)

-- SQL `<>` (not-equal), at comparison precedence.
macro:50 a:term:51 " <> " b:term:51 : term =>
  `($a != $b)

-- SQL `x IN (a, b, …)` desugars to an `OR`-chain of equalities.
macro:50 x:term:51 " IN " "(" elems:term,+ ")" : term => do
  let cmps ← elems.getElems.mapM fun e => `($x == $e)
  cmps.foldlM (fun acc c => `($acc || $c)) (← `(false))

-- SQL `x NOT IN (a, b, …)` — negation of `IN`.
macro:50 x:term:51 " NOT " " IN " "(" elems:term,+ ")" : term => do
  let cmps ← elems.getElems.mapM fun e => `($x == $e)
  let chain ← cmps.foldlM (fun acc c => `($acc || $c)) (← `(false))
  `(!($chain))

-- SQL `x BETWEEN a AND b` (inclusive). The inner `AND` is part of BETWEEN; the `:51` args keep the
-- boolean `AND` macro (prec 30) from swallowing it.
macro:50 x:term:51 " BETWEEN " a:term:51 " AND " b:term:51 : term =>
  `($a ≤ $x && $x ≤ $b)

-- SQL `x LIKE pat` — string match with `%`/`_` wildcards. `strLike` lives in `Operators/Like.lean`
-- (not imported here, to keep `Syntax` pure), so emit a raw ident that resolves at the use-site.
macro:50 x:term:51 " LIKE " p:term:51 : term =>
  `($(Lean.mkIdent (`LeanDatabase ++ `strLike)) $p $x)

-- SQL `EXISTS (subquery)` / `NOT EXISTS (subquery)` — correlated; intercepted as a `WHERE` form by
-- `Parser.Query` (→ `semijoin` / `antijoin`), so this syntax is only ever matched, never elaborated.
syntax:90 "EXISTS" "(" sql_query ")" : term
syntax:90 "NOT" "EXISTS" "(" sql_query ")" : term

-- SQL `x IN (subquery)` / `x NOT IN (subquery)` — also intercepted by `Parser.Query` (→
-- `semijoin`/`antijoin` on the implicit equality `x = innerColumn`). Distinct from the IN-list forms.
syntax:90 term:91 " IN " "(" sql_query ")" : term
syntax:90 term:91 " NOT " " IN " "(" sql_query ")" : term

-- `t:term:50` (comparison level) so `NOT` binds looser than `=`/`<`/`>` but tighter than `AND`/`OR`:
-- `NOT a = b` is `NOT (a = b)`, and `NOT a AND b` is `(NOT a) AND b` — matching SQL precedence.
macro:85 "NOT" t:term:50 : term =>
  `(!$t)

/-!
## Macros to turn aggregates into variable names.
-/
macro "SUM" "(" p:ident ")" : term => return mkIdent (p.getId ++ `sum)
macro "COUNT" "(" p:ident ")" : term => return mkIdent (p.getId ++ `count)
macro "AVG" "(" p:ident ")" : term => return mkIdent (p.getId ++ `avg)
macro "MIN" "(" p:ident ")" : term => return mkIdent (p.getId ++ `min)
macro "MAX" "(" p:ident ")" : term => return mkIdent (p.getId ++ `max)
macro "COUNT" "(" "*" ")" : term => return mkIdent `countAll

open Meta Elab Term
def expandStx (str: String) : TermElabM Format := do
  let .ok stx := Parser.runParserCategory (← getEnv) `sql_query str | throwError "Failed to parse SQL query: {str}"
  let stx ← escapeJoin stx
  PrettyPrinter.ppCategory `sql_query stx

-- #eval expandStx "SELECT * FROM table JOIN table2 ON table.age = table2.age WHERE table.age > 30 && table.isActive && table.height < 180"

end LeanDatabase
