# Roadmap: from 2.6% to 100% of `crossskill_equivalent_sql.jsonl`

Target corpus: **351 records / 1266 queries**. A record counts as *covered* only when **every** variant
in it parses and elaborates, since equivalence is proved per variant-pair.

Baseline today: **33 / 1266 queries (2.6%)**, **2 / 351 records (0.6%)**.

---

## The chosen semantics (decided)

**We commit to set semantics: `TypedRelation.rows : Finset`, and we assume every base table has
distinct rows.** Equivalence therefore means *"the two queries denote the same result set."* We are
**not** building the `Multiset` (bag) or `List` (ordered) layers — that decision is final, and the
Multiset phases below (0.4–0.6) are struck out accordingly.

This is a real spec, not a fudge, but it draws a hard boundary. Under "same result set":

| construct | status under our spec | why |
|---|---|---|
| `DISTINCT` | **identity** (sound) | every relation is already a set |
| `ORDER BY` | **identity** (sound) | row order is not observable on a `Finset` |
| `UNION ALL` | **= `UNION`** (sound *as sets*) | the result *set* of a bag-union is its set-union |
| `WHERE` / `JOIN` / `GROUP BY` / scalar aggregates | faithful | set-relational algebra |
| `LIMIT k` | **cannot be modelled** (see Bug 0.B) | picking *which* k rows needs an order we don't have |
| window fns (`ROW_NUMBER`, `RANK`) | **out of scope by design** | meaningless without row order |
| `COUNT(*)` / `SUM` over duplicates | approximated (set-count) | duplicates are gone; the distinct-rows assumption covers base tables, not derived ones |

So the honest coverage ceiling is **not 100%**. Window functions (27% of the corpus) and true
top-N-by-`LIMIT` semantics are permanently out of scope. The reachable target is **the Phase 5 line
— ~73% of queries / ~68% of records** (see the curve below). Everything past that needs a semantics
we've chosen not to build.

Dependency spine: `Phase 0 (soundness)` → `Phase 4 (NULL)` → `Phase 5 (outer joins)`. Phases 1–3 are
independent and can proceed in parallel. Phase 6 (windows) is **dropped**.

---

## Coverage unlock curve (measured, not estimated)

| after phase | queries OK | records fully OK |
|---|---|---|
| P0 baseline (today) | 33 (2.6%) | 2 (0.6%) |
| P1 cheap syntax | 95 (7.5%) | 13 (3.7%) |
| P2 opaque scalars | 213 (16.8%) | 34 (9.7%) |
| P3 CTE | 557 (44.0%) | 112 (31.9%) |
| P4 NULL + 3VL | 782 (61.8%) | 184 (52.4%) |
| P5 outer joins | 926 (73.1%) | 238 (67.8%) |
| ~~P6 window functions~~ | ~~1266 (100%)~~ | **out of scope (needs row order)** |

**P5 (73.1% / 67.8%) is the ceiling under set semantics**, not a waypoint to 100%. The last ~27% of
queries use window functions, which cannot be modelled on a `Finset`.

**P3 (CTE) is the single biggest unlock: +27.2 points of queries.** It is also cheap relative to
P4. If only one phase ships, ship P3.

> Note on `LIMIT`: queries with `ORDER BY … LIMIT k` still *parse* and count toward the curve, and an
> equivalence closes when both sides carry the *same* `LIMIT k` over congruent subqueries (via
> `limit_congr`, Phase 0). What is out of scope is a *top-N semantic* equivalence — two variants that
> differ in how `LIMIT` selects rows. Those need the ordered layer we chose not to build.

---

# Phase 0 — Soundness (BLOCKING; do not add features on a broken base)

Under the set-semantics decision, the two items from the audit split apart: one dissolves, one is a
genuine bug even in our own model.

### 0.A — `UNION ALL` aliased to set `union` — **SOUND under our spec; scoping only**
`Parser/Query.lean:85` maps both `UNION` and `UNION ALL` to `` `union ``. Under bag semantics this
would be wrong (`t UNION ALL t` doubles rows). **But we chose set semantics**, where a query denotes
its *result set*, and the result set of `t UNION ALL t` genuinely *is* `t`. So `sql_equiv` proving
`SELECT a FROM t UNION ALL SELECT a FROM t = SELECT a FROM t` is **correct w.r.t. our spec** — not a
bug. The only residual risk is a reader mistaking `=` for bag-equality. Fix is documentation +
naming (0.2), not behaviour. (Known scope limit: a `COUNT(*)` over a `UNION ALL` counts distinct,
not bag — accepted, listed in the semantics table.)

### 0.B — `LIMIT k` is the identity — **GENUINE BUG, even in set semantics**
`Operators/OrderLimit.lean:38-44`: `limit k rel = rel`, `@[simp, grind =]`. This is false *as sets*:
`LIMIT 1` on a 2-row table is a 1-row set ≠ the 2-row set. `sql_equiv` proves
`SELECT * FROM t LIMIT 1 ≡ SELECT * FROM t`. **`Example18` is a live instance** — it asserts
`… ORDER BY age LIMIT 10 = SELECT * FROM table`. `LIMIT` genuinely cannot be modelled on a `Finset`
(no order to pick "first k"), so the honest move is to make it **opaque** — provably equal only to
itself — never the identity.

Contrast with `orderBy`: identity **is** sound under set semantics (order unobservable), so
`orderBy_eq` stays tagged. 0.B touches `limit` only.

### Tasks

- [x] **0.1 Make `limit` opaque (S) — the fix. ✅ DONE.** `Operators/OrderLimit.lean`: `def limit`
      → `opaque limit`, deleted `limit_eq` / `limit_card` / `limit_noop_of_card_le`, added
      `limit_congr : r1 = r2 → limit k r1 = limit k r2`. `SQLEquiv.lean`: added
      `| refine limit_congr ?_` as the first alternative in `sql_equiv`. `Example18` fixed (both
      sides carry `LIMIT 10`; now a true theorem). `limit k t = t` is no longer provable. `orderBy`
      left as sound identity.
- [ ] **0.2 Name the claim honestly (S).** The elaborator proves *set-equivalence*. Reflect it:
      `SetSemantics.query_equivalence`, or a doc-comment convention on each example, so `sql%(…) =
      sql%(…)` is never misread as bag/ordered SQL equality. This is also where 0.A is discharged —
      the `UNION ALL` note lives here.
- [ ] **0.3 Distinct-rows discipline (M).** The blanket "base tables have distinct rows" assumption
      makes set = bag *at the leaves* (so `SUM`/`COUNT` over a base table are honest). Make it
      real, not just prose: an optional `PRIMARY KEY` on `CREATE TABLE` emitting
      `hkey : Function.Injective (key)`, available as a hypothesis where a proof needs it (e.g. to
      justify `SUM` not double-counting). Does **not** extend to derived tables — a `UNION ALL`
      feeding an aggregate is still set-count.
<!-- - [ ] **0.4 Multiset core (XL — the real fix).** Change `TypedRelation.rows` to `Multiset`.
      `LeanDatabase/ListRelationalAlgebra/TypedListRelation.lean` is already a half-built version of
      this: `List` + `List.Perm` setoid + `toFinsetRelation`, and it carries `LinearOrder` on columns
      (which Phase 6 needs). **It is orphaned — nothing imports it — and `RelationalAlgebraList.lean`
      has 16 `sorry`s.** Decide: finish that file, or fold it into the main tower and delete it. Do
      not leave a third parallel algebra.
      Blast radius: 136 `Finset` occurrences, 201 theorems, 140 `@[grind]`/`@[simp]` lemmas,
      30 example files to re-prove.
- [ ] **0.5 Re-tag the automation (L).** `Finset.filter_filter` / `Finset.image_image` in `sql_simp`
      become `Multiset` analogues. Re-audit all 140 tagged lemmas: **every lemma that assumed dedup
      is now either false or needs a `Nodup` hypothesis.** This is where the real work is.
- [ ] **0.6 `DISTINCT` becomes the only route to `Finset` (M).** `distinct` (`Operators/Select.lean`)
      is the coercion `Multiset → Finset`. Re-derive the set-level lemmas as
      `distinct`-conditioned corollaries so existing proofs survive as special cases. -->
<!-- - [ ] **0.7 Ordered top layer (M).** DROPPED — requires the `List` layer we chose not to build.
      `ORDER BY` stays identity (sound); `LIMIT` stays opaque (0.1). -->
- [ ] **0.8 Regression guard (S).** Script that runs the corpus and prints `queries OK / records OK`.
      Wire into CI so coverage is a tracked number, not a claim.

---

# Phase 1 — Cheap syntax (2.6% → 7.5%)

- [x] **1.1 `ORDER BY … ASC|DESC` (S). ✅ DONE.** Added `sql_order_dir` (`ASC`/`DESC`) and
      `sql_order_item` (= `sql_col` + optional dir) categories in `Parser/Syntax.lean`; `ORDER BY`
      now takes `sql_order_item,*`; `Parser/Query.lean` strips the direction via `sqlOrderCol` and
      elaborates to the existing identity `orderBy`. Direction is provably erased
      (`ORDER BY a DESC = ORDER BY a ASC = unordered`, verified). Unblocks the **60.1%** of queries
      that were dying at parse time on a direction token.
- [ ] **1.2 Qualified star `t.*` (S).** 1.3% of queries. Expand against the schema.
- [ ] **1.3 `CASE … END` without `ELSE` (S, partial).** 10.6% of queries. Full semantics is
      `ELSE NULL` → belongs to Phase 4. **But** the dominant idiom is
      `COUNT(CASE WHEN p THEN 1 END)` (2.1% of queries), where `COUNT` skips `NULL`. Handle *only*
      the aggregate-argument position now via `sum_indicator_eq_count_where`
      (`Operators/Aggregate.lean:77`), and **error** on the general position rather than defaulting
      to `0` — defaulting to `0` is silently wrong for `SUM`/`AVG`/`MIN`.

---

# Phase 2 — Opaque scalar functions (7.5% → 16.8%)

`ROUND` 22.2%, `CAST`/`::` 33.3%, date fns 17.1%, string fns 13.4%. These almost always appear
*identically on both sides* of an equivalence, so they cancel and need no axioms.

- [ ] **2.1 `ScalarKind` registry (M).** Copy the `AggKind` pattern from `Parser/Context.lean` —
      it is the right design and it earned its keep (10 aggregates, one builder). One enum + one
      `elabScalarE` dispatcher. Do **not** add these one macro at a time.
- [ ] **2.2 Uninterpreted-by-default (S).** Each scalar fn elaborates to an opaque Lean function.
      Cancellation is then `rfl`/congruence — no semantics needed.
- [ ] **2.3 Targeted axioms only where variants differ (M).** `ABS(a-b) = ABS(b-a)`; `ROUND`
      idempotence. **Do not** axiomatize `ROUND(x,12) = ROUND(x,2)` or `SUBSTR ≡ RIGHT` — those are
      data-dependent and belong to Phase 8.
- [ ] **2.4 `CAST` is not free (M).** `CAST(int AS float)` changes division semantics. Integer vs
      real division is a genuine expected-FAIL in the existing plan (`sf_bq030`). Model `CAST` as a
      real coercion, not an opaque function, or it will launder integer-division bugs.

---

# Phase 3 — CTE (16.8% → 44.0%) ← **biggest unlock, do this first after Phase 1**

`WITH` appears in **76.6%** of queries. Only **3 queries (0.2%) use `WITH RECURSIVE`** — so the
recursive fixpoint, the genuinely hard part, is almost pure ignorable tail.

- [ ] **3.1 Grammar (S).** `WITH x AS (q), y AS (q) SELECT …`, comma-separated, non-recursive.
- [ ] **3.2 Elaborate as `let` (M).** A CTE is a local relation binding, not a new operator. Reuse
      the existing `withLetDecl` machinery in `Parser/Context.lean`. Bind once, reference `n` times.
- [ ] **3.3 Make `grind` see through it (M).** Either inline CTEs at elaboration (simple, may blow up
      term size when referenced many times) or keep the `let` and add a `zeta`-reduction step to
      `sql_simp`. Start with inlining; measure term size before optimizing.
- [ ] **3.4 Scalar subquery in `SELECT` (L).** **71.2%** of queries. `(SELECT SUM(x) FROM t)` in a
      select-list is an ungrouped aggregate → `relSum`/`relCount`. This was deferred earlier as
      "a bit too complex"; at 71% it is no longer optional. Correlated scalar subqueries are harder
      than uncorrelated — split the task and do uncorrelated first.
- [ ] **3.5 `WITH RECURSIVE` (XL).** 3 queries. **Explicitly deprioritize**; log as out of scope.

---

# Phase 4 — `NULL` and three-valued logic (44.0% → 61.8%)

`NULL` appears in **31.3%** of queries; `IS [NOT] NULL` in **29.9%**. This is the second-hardest
phase and it cannot be faked.

- [ ] **4.1 Nullable types (M).** `SQLTypeProxy` gains nullability; column type becomes `Option τ`.
- [ ] **4.2 Predicates become Kleene (L).** `WHERE` currently takes `Bool`. It must take
      `Option Bool` (or a 3-valued `SQL3` inductive). `WHERE p` keeps rows where `p = some true` —
      `NULL` is *not* kept. Rewrite `pAnd`/`pOr`/`pNot` (`RelationalAlgebra.lean`) to Kleene tables.
      **Every predicate lemma in the codebase must be re-proved.** Adding `NULL` as a value without
      doing this creates a soundness hole of exactly the same shape as Bug 0.A.
- [ ] **4.3 `IS NULL` / `IS NOT NULL` (S).** These are 2-valued even on `NULL` input — the escape
      hatch out of Kleene logic.
- [ ] **4.4 `COALESCE`/`IFNULL`/`NULLIF` (S).** 14.1%. Trivial once 4.1 lands.
- [ ] **4.5 Aggregates skip `NULL` (M).** `COUNT(x)` ignores nulls, `COUNT(*)` does not.
      `SUM` of all-nulls is `NULL`, not `0`. `AVG` divides by the non-null count. Each is a separate
      lemma; the `AggKind` registry makes this a per-kind field rather than 10 rewrites.
- [ ] **4.6 The `NULL` equality quirk (M).** `NULL = NULL` is *unknown* in `WHERE`, but `GROUP BY`
      and `DISTINCT` treat nulls as **equal** (one group, one row). Two different equalities on the
      same type. This will bite; encode it explicitly rather than letting `DecidableEq` decide.
- [ ] **4.7 `CASE` without `ELSE` (S).** Now correctly `ELSE NULL`. Retires the Phase 1.3 debt.

---

# Phase 5 — Outer joins (61.8% → 73.1%) — depends on Phase 4

`LEFT JOIN` 14.9%; `RIGHT`/`FULL` only 1.4%.

- [ ] **5.1 `LEFT JOIN` (L).** Null-pad unmatched left rows. Requires 4.1. Do left first; `RIGHT` is
      `LEFT` with arguments swapped, `FULL` is the union of both.
- [ ] **5.2 The pushdown lemma (M).** `LEFT JOIN` + `WHERE` on a right-hand column ≡ `INNER JOIN`.
      This is *the* rewrite optimizers make and the one the corpus will test.
- [ ] **5.3 Join commutativity/associativity (M).** Already a known gap (`sf_bq060`, expected FAIL in
      the current plan). Needs the `Fin.append` index-swap lemma. Unblocks inner-join reordering,
      which the corpus exercises constantly.

---

# Phase 6 — Window functions — **OUT OF SCOPE (dropped with the `List` layer)**

`OVER(…)` 26.9%; `PARTITION BY` 17.6%; `ROW_NUMBER` 17.8%; `RANK`/`DENSE_RANK` 2.1%.

`ROW_NUMBER()`/`RANK()` are **meaningless on a `Finset`** — they need row order, which set semantics
discards. These are permanently out of scope under the chosen spec and are why the ceiling is ~73%,
not 100%. A query containing a window function is logged as *out-of-scope-by-design*, not attempted.

**Exception worth a second look — aggregate windows without `ORDER BY` (4.3%).** `SUM(x) OVER
(PARTITION BY k)` has no row-order dependence: it is a per-group aggregate broadcast back onto every
row. It *is* expressible on a `Finset` (reuse the `groupBy` machinery + a join back to rows). If any
window support is ever added, it is only this slice — and it belongs in Phase 4/5 territory, not a
revived Phase 6.

---

# Phase 7 — Proof automation (cross-cutting, continuous)

- [ ] **7.1 Parser emits clean group keys (M).** ("Fix 4" from earlier.) Emit
      `groupByRel key labels mkRow base` with `fun t => t 0` instead of opaque
      `TypedTupleOfList.cons` keys. This shrinks `Example12`'s `hpres` from ~10 lines to one.
- [ ] **7.2 Opt-in `group_equiv` tactic (M).** The blanket `sql_simp` unfold of `mapByList`/`map` was
      tried and **broke 7 previously-passing proofs** (`Sf010`, `Sf_bq398`, `Example6`, `Example11`,
      `Example18`, `Example20`). Do not retry it globally. A dedicated whole-relation `GROUP BY`
      tactic is the right home. Note `SQLEquiv.lean` does not import `Parser.Context`, so it cannot
      name `mapByList` — the tactic must live above the parser.
- [ ] **7.3 Counterexample search (M).** Wire `plausible` into `sql_equiv` so a *false* equivalence
      fails fast with a witness instead of timing out. This is the direct defense against Bugs 0.A/
      0.B ever recurring: a bag-semantics counterexample generator would have caught both.
- [ ] **7.4 Normal-form pass (L).** Push `WHERE` through joins/unions, fold `SUM(CASE)`→`WHERE`+`SUM`,
      canonicalize `IN`→`OR`-chain, before `grind`. Turns many equivalences into `rfl`.

---

# Phase 8 — Data-dependent hypotheses (orthogonal; user-deferred)

Some corpus pairs are equal **only under assumptions absent from the SQL and DDL**, e.g. `sf_bq327`
(`COUNT(DISTINCT indicator_name)` vs `COUNT(DISTINCT indicator_code)` — needs a name↔code bijection),
`sf_bq232` (dropping `major_category` — needs a functional dependency), `state='FL'` vs
`state_name='Florida'`. These are **not** provable by any amount of the above and must not be.

- [ ] **8.1 Hypothesis vocabulary (M).** intra-column (`0 ≤ age ≤ 100`), inter-column
      (`salary = months * wage`), functional dependency (`minor → major`), bijection (`name ↔ code`).
- [ ] **8.2 Surface them in `CREATE TABLE` (M)** so they become theorem hypotheses, not axioms.
- [ ] **8.3 Feed them to `grind` (M).**
- [ ] **8.4 Ledger (S).** Classify every corpus record: *pure-algebra* / *needs-hypothesis* /
      *genuinely-not-equivalent*. Nobody should be scored against pairs in the third bucket.

---

# Suggested execution order

Coverage per unit of effort, respecting the dependency spine:

1. **0.1, 0.2, 0.8** — stop the bleed, rename the claim, start measuring. Days, not weeks.
2. **1.1–1.3** — cheap parse wins (2.6% → 7.5%). Unblocks the 60% of queries dying on `DESC`.
3. **3.1–3.4** — CTE + scalar subquery (**→ 44%**). Best return in the entire roadmap.
4. **2.1–2.4** — scalar registry (→ ~50% combined with P3).
5. **0.3** — key hypothesis; retro-legitimizes existing examples cheaply.
6. **7.1, 7.3** — clean keys + counterexample search. 7.3 (`plausible`) is the standing guard that
   would have caught Bug 0.B automatically — wire it in early.
7. **4.x** → **5.x** — NULL, then outer joins. This is the ceiling (~73% / 68%).
8. **8.x** — data-dependent hypotheses, for the pairs inside that ceiling that need them.

Window functions (old Phase 6) and top-N-`LIMIT` semantics are **not on this list** — out of scope
by the set-semantics decision.

**If you do only one thing:** 0.1 (make `limit` opaque). It is the one place `sql_equiv` proves
something false *in our own model*, and `Example18` is currently that false thing wearing a green
checkmark. An automated prover that proves false things is worse than no prover, because it is
believed.

**If you do only one *feature*:** Phase 3 (CTE). +27 points, no semantic prerequisites.
