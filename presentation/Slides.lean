import VersoSlides
import Verso.Doc.Concrete

open VersoSlides

set_option verso.code.warnLineLength 500

#doc (Slides) "LeanDatabase" =>

# {class "kicker"}[QUERY CONSOLE] LeanDatabase
%%%
backgroundColor := "#211c17"
%%%


*Machine-checked SQL query equivalence, in Lean 4*

Write two SQL queries. Ask Lean whether they're *provably* the same relation.

:::notes
Opening slide. Introduce yourself, then frame the talk: this is a Lean4 project that
formalizes SQL semantics well enough to *prove* — not test, not sample — that two queries
always return the same rows.
:::

# {class "kicker"}[THE PROBLEM] Why Would You Want This?

A query optimizer rewrites `A` into `B` for performance. *Is `A ≡ B`, always?*

* Unit tests check a handful of inputs.
* This project checks *every* input, by proof.

:::fragment
LeanDatabase is a case study in a bigger idea: treat program synthesis as a *checkable*
process — an LLM (or a human) proposes a query rewrite, and Lean either proves it correct
or refuses to.
:::

:::notes
This is the "Verified AI" framing from VerifiedAI.md — program synthesis plus automated
proof of properties, with SQL as the concrete instance. Don't over-dwell; one breath, then
move into the examples.
:::

# {class "kicker"}[EXAMPLES] Five Proofs
%%%
backgroundColor := "#211c17"
%%%


Simple to impressive. Every one is a *real theorem*, checked by the kernel.

# {class "kicker"}[EXAMPLE 1 / 5] Boolean Algebra
%%%
vertical := true
%%%

`Examples/Example0.lean` — ten laws, one file, every one a bare `sql_equiv`.

## De Morgan

:::::hstack
```code sql
SELECT * FROM table
WHERE NOT (age > 30 OR isActive)
```

:::attr («class» := "equiv-mark")
≡
:::

```code sql
SELECT * FROM table
WHERE NOT (age > 30)
  AND NOT isActive
```
:::::

## Absorption

:::::hstack
```code sql
SELECT * FROM table
WHERE isActive
   OR (isActive AND age > 30)
```

:::attr («class» := "equiv-mark")
≡
:::

```code sql
SELECT * FROM table
WHERE isActive
```
:::::

# {class "kicker"}[EXAMPLE 2 / 5] `UNION` Distributes Over `WHERE`

*The "MapReduce rewrite" —* `Examples/Example1.lean`

:::::hstack
```code sql
SELECT * FROM
  (SELECT * FROM r1
   UNION
   SELECT * FROM r2)
WHERE is_high_value
```

:::attr («class» := "equiv-mark")
≡
:::

```code sql
SELECT * FROM r1
  WHERE is_high_value
UNION
SELECT * FROM r2
  WHERE is_high_value
```
:::::

:::fragment
Filter-then-union equals union-then-filter — the rewrite that makes a filter
*parallelizable across shards*. Both boxes above are *literal Lean source text* —
`sql_equiv` decides which side of "≡" is true, as a Lean tactic.
:::

# {class "kicker"}[EXAMPLE 3 / 5] `EXISTS` ≡ `IN`

*Semi-join duality —* `Examples/Example5.lean`

:::::hstack
```code sql
SELECT * FROM customers c
WHERE EXISTS (
  SELECT 1 FROM orders o
  WHERE o.customer_id
      = c.customer_id)
```

:::attr («class» := "equiv-mark")
≡
:::

```code sql
SELECT * FROM customers c
WHERE c.customer_id IN (
  SELECT customer_id
  FROM orders)
```
:::::

:::fragment
A correlated subquery and a set-membership test — not obviously the same query to a
non-expert, instantly checkable to Lean.
:::

# {class "kicker"}[EXAMPLE 4 / 5] `JOIN` Pushdown

*A classic optimizer rewrite —* `Examples/ExampleComplex2.lean`

:::::hstack
```code sql
SELECT * FROM
  (SELECT * FROM employees
   WHERE salary > 50000) AS e
JOIN departments
  ON e.dept_id
   = departments.dept_id
WHERE departments.budget
    > 100000
```

:::attr («class» := "equiv-mark")
≡
:::

```code sql
SELECT * FROM employees
JOIN departments
  ON employees.dept_id
   = departments.dept_id
WHERE employees.salary
    > 50000
  AND departments.budget
    > 100000
```
:::::

:::fragment
Honest caveat found while building this: the grammar only allows `JOIN`ing a bare table
— the *right* side of `JOIN` can't be a subquery. Left-side pushdown only.
:::

# {class "kicker"}[EXAMPLE 5 / 5] The Finale

*Four laws, one proof —* `Examples/ExampleComplex1.lean`

:::::hstack
```code sql
(SELECT * FROM
  (SELECT * FROM orders
   WHERE region = "US") AS a
 WHERE NOT (NOT (amount > 100))
   AND status = "completed")
UNION
(SELECT * FROM
  (SELECT * FROM orders
   WHERE region = "EU") AS b
 WHERE amount > 100
   AND status = "completed")
```

:::attr («class» := "equiv-mark")
≡
:::

```code sql
SELECT * FROM orders
WHERE (region = "US"
    OR region = "EU")
  AND amount > 100
  AND status = "completed"
```
:::::

Cascading `WHERE`, double negation, `UNION` ≡ `OR`, and `AND` reordering — chained into
*one* `sql_equiv` call.

# {class "kicker"}[LIVE DEMO] Try It Yourself
%%%
backgroundColor := "#211c17"
%%%


`sql_server.py` wraps the compiled `sql_process` executable behind a small HTTP demo —
the same `sql_equiv` engine from every example, live in a browser.

# {class "kicker"}[LIVE DEMO] How It Works

Type two queries, pick a schema, click *Check equivalence*. The page shows the exact
JSON sent to Lean and the exact JSON it returns — a real round trip, screenshotted live:

{image "demo-images/live-demo.png" (width := "720px")}[Screenshot of the running LeanDatabase SQL Equivalence demo, showing a query pair, the JSON request, and a JSON response of equivalent true.]

:::fragment
Same tactic, same lemma library, same kernel check — just wrapped in a web page instead
of a `.lean` file.
:::

# {class "kicker"}[UNDER THE HOOD] How Does This Actually Work?
%%%
backgroundColor := "#211c17"
%%%


Five layers, and three design choices worth explaining.

# {class "kicker"}[ARCHITECTURE] Five Layers

:::table +colHeaders +rowSeps
*
  * Layer
  * File(s)
  * Job
*
  * Data model
  * `TypedRelation.lean`
  * Tables as typed `Finset`s of rows
*
  * Operators
  * `Operators/*.lean`
  * `restriction`, `join`, `groupBy`, `select`, …
*
  * Parser
  * `Parser/*.lean`, `SQLSyntax.lean`
  * SQL text → real Lean terms
*
  * Automation
  * `SQLEquiv.lean`, `SQLToolbox.lean`
  * The `sql_equiv` tactic + lemma library
*
  * Examples
  * `Examples/*.lean` (23 files)
  * Proved rewrites — *and* the test suite
:::

# {class "kicker"}[DESIGN CHOICE 1] Tables Are `Finset`s

```code haskell
@[ext, grind cases]
structure TypedRelation (colType : Fin n → Type) [∀ i, DecidableEq (colType i)] where
  labels : Fin n → String
  rows   : Finset (TypedTuple colType)
```

:::frame
"We use `Finset` ... which allows us to compute cardinality and guarantees
finiteness, unlike `Set`."
— `TypedRelation.lean`
:::

:::fragment
`union` is `∪`. `restriction` (`WHERE`) is `Finset.filter`. `projection` (`SELECT`) is
`Finset.image`. *Every Mathlib `Finset` lemma is now a SQL lemma, for free.*
:::

# {class "kicker"}[DESIGN CHOICE 1] The Honest Tradeoff

`Finset` has no duplicates — so this model is exact *when your data is deduplicated*.

:::frame
`COUNT`/`SUM` over distinct rows agree with SQL's bag semantics *only* under that
assumption — several examples state it as an explicit precondition (e.g. sharded
tables must be *disjoint* before a `SUM` distributes over their `UNION`).
:::

Set semantics bought a huge lemma library. The price is written down, not hidden.

# {class "kicker"}[DESIGN CHOICE 2] Parse Real SQL Text

Why not just write relational-algebra terms by hand?

* An LLM (or a human) writes *SQL*, not Lean terms.
* The parser is *itself* part of what gets exercised by every example.

```code haskell
def parseSqlQuery (schemas) (query : String) : TermElabM (Expr × ...) :=
  -- runs `query` through Lean's own parser, as a custom syntax category
```

:::fragment
The SQL string in a theorem is not documentation. It is the input.
:::

# {class "kicker"}[DESIGN CHOICE 2] From String to Term

:::::hstack
::::vstack
:::frame
*Parse* — as *Lean syntax*, a custom `sql_query` grammar
:::
:::frame
*Desugar `JOIN`* — into comma-product + `WHERE`
:::
:::frame
*Resolve names* — `age` → `table.age`, via the schema
:::
::::

::::vstack
:::frame
*Elaborate* — `WHERE` → `restriction`, `SELECT` → `mapByList`, …
:::
:::frame
*Result* — an ordinary, type-checked `TypedRelation` term
:::
::::
:::::

:::fragment
No separate interpreter. `sql_equiv` can `simp`/`grind` on the result because it's just
ordinary Lean.
:::

# {class "kicker"}[DESIGN CHOICE 3] `sql_equiv`, in Full

This is the *entire* tactic. Not a summary — the actual source.

```code haskell
macro "sql_simp" : tactic => `(tactic| simp_all [Finset.filter_filter, Finset.image_image])

macro "sql_equiv" : tactic => `(tactic|
  (
   repeat (first
     | (apply TypedRelation.ext <;> try rfl)
     | refine Finset.filter_congr (fun _ _ => ?_)
     | refine Finset.image_congr (fun _ _ => ?_)
     | sql_simp
     | (apply funext; intro _))
   all_goals (first
     | grind +locals
     | (apply Finset.ext; sql_simp; grind +locals))))
```

:::fragment
No relational-algebra normal-form algorithm. No custom decision procedure. Ten lines of
tactic combinators.
:::

# {class "kicker"}[DESIGN CHOICE 3] Why Not a Decision Procedure?

The intelligence lives in the *lemma library*, not the tactic:

:::frame
"A curated, *confluent* set of relational-algebra identities... no
commutativity/associativity (those would loop), and no two rules sharing a
left-hand side."
— `SQLToolbox.lean`
:::

:::fragment
New SQL feature → add lemmas to one more `Operators/*.lean` file. The tactic never
changes.
:::

# {class "kicker"}[HONEST LIMITATIONS] What This Can't Do
%%%
backgroundColor := "#16302e"
%%%


Things this project documents about itself, on purpose:

* `ROW_NUMBER()` is *not modeled* — nondeterministic under ties, so it's left out
  rather than given a wrong definition.
* Cross-table *functional dependencies* must be supplied as explicit hypotheses —
  `sql_equiv` cannot discover `country_code → country_name` on its own.
* Not every example is a bare `sql_equiv` call: `Example12.lean`'s `SUM(CASE...)` rewrite
  needs a human-supplied bridging lemma, since the two `GROUP BY`s scan different base
  relations — a gap automation can't close on its own.
* One proof needs `set_option maxHeartbeats 1000000` — automation isn't free.
* A block of *AI-generated `JOIN`-desugaring rules* is left in the source, commented
  out, next to the hand-fixed version that's actually used.

:::fragment
Every one of these is written down in the code, not swept under the rug.
:::

# {class "kicker"}[WHAT'S NEXT] Three Directions

* `plausible` (counterexample search) is already a transitive dependency —
  *disproof* is architected for, not yet wired up.
* `JOIN`'s right-hand side is currently restricted to bare tables.
* Window functions (`ROW_NUMBER`, `RANK`, …) are the natural next modeling target.

# {class "kicker"}[QUERY CONSOLE] Thank You
%%%
backgroundColor := "#211c17"
%%%


*LeanDatabase* — SQL rewrites you can trust because the kernel checked them.

:::fragment
Questions?
:::

:::notes
Close by looping back to the opening framing: this isn't really about SQL specifically —
it's a worked example of "LLM proposes, Lean disposes."
:::
