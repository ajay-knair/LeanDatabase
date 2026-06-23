import Lean

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

syntax "SELECT" sql_cols "FROM" sql_from ("WHERE" term)? (";")? ("GROUP" "BY" sql_cols ("HAVING" term)?)? : sql_query

macro_rules -- Gemini generated (then fixed) rules for desugaring JOINs and CROSS JOINs into comma-separated FROM clauses with WHERE conditions; GROUP BY omitted for now.
  -----------------------------------------------------------------------------
  -- CASE A: The query ALREADY has an existing WHERE clause
  -----------------------------------------------------------------------------
  -- 1. Desugar INNER JOIN -> Replace with comma, append condition via AND

  | `(sql_query| SELECT $items FROM $f:sql_from JOIN $tNext:ident ON $onCond WHERE $whereCond $[;]?) =>
      `(sql_query| SELECT $items FROM $f, $tNext:ident WHERE $whereCond AND $onCond;)

  -- 2. Desugar CROSS JOIN -> Replace with comma, leave WHERE unchanged

  | `(sql_query| SELECT $items FROM $f:sql_from CROSS JOIN $tNext:ident WHERE $whereCond $[;]?) =>
      `(sql_query| SELECT $items FROM $f, $tNext:ident WHERE $whereCond ;)

  -----------------------------------------------------------------------------
  -- CASE B: The query does NOT have a WHERE clause yet
  -----------------------------------------------------------------------------
  -- 3. Desugar INNER JOIN -> Initialize the WHERE clause with the ON condition

  | `(sql_query| SELECT $items FROM $f:sql_from JOIN $tNext:ident ON $onCond $[;]?) =>
      `(sql_query| SELECT $items FROM $f, $tNext:ident WHERE $onCond ;)

  -- 4. Desugar CROSS JOIN -> Replace with comma, no WHERE clause needed

  | `(sql_query| SELECT $items FROM $f:sql_from CROSS JOIN $tNext:ident $[;]?) =>
      `(sql_query| SELECT $items FROM $f, $tNext:ident;)


partial def getIdents (stx : TSyntax `sql_from) : List Name :=
  match stx with
  | `(sql_from| $db:ident) => [db.getId]
  | `(sql_from| $f1:sql_from , $f2:sql_from) => getIdents f1 ++ getIdents f2
  | _ => []

/-! ## Term-level `WHERE`-predicate combinators -/

macro "SELECT" " * " "FROM" ident "WHERE" t:term : term =>
    return t

macro:30 t:term "AND" s:term : term =>
  `($t && $s)

macro:30 t:term "OR" s:term : term =>
  `($t || $s)

macro:85 "NOT" t:term : term =>
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

end LeanDatabase
