import LeanDatabase.Parser
open LeanDatabase

/-!
# Cross-skill instance `sf_bq060`

**Question:** Which top 3 countries had the highest net migration in 2017 among those with an area greater than 500 square kilometers? And what are their migration rates?

Variants claimed equivalent: 4. Tables encoded (full schema): BIRTH_DEATH_GROWTH_RATES, COUNTRY_NAMES_AREA

## variant [semantic-probing-1-pass]
```sql
SELECT b."country_name", b."net_migration"
FROM "…"."BIRTH_DEATH_GROWTH_RATES" b
JOIN "…"."COUNTRY_NAMES_AREA" c ON b."country_code" = c."country_code"
WHERE b."year" = 2017 AND c."country_area" > 500
ORDER BY b."net_migration" DESC LIMIT 3;
```

## variant [probing-1-pass]
```sql
SELECT c."country_name", b."net_migration"
FROM "…"."BIRTH_DEATH_GROWTH_RATES" b
JOIN "…"."COUNTRY_NAMES_AREA" c ON b."country_code" = c."country_code"
WHERE b."year" = 2017 AND c."country_area" > 500
ORDER BY b."net_migration" DESC LIMIT 3;
```

(baseline-sg / baseline-1 are identical up to aliasing; they project `country_name` from `b` and
from `a`=CNA respectively.)

**Difference (winnable pair) — IN-SCOPE under a stated cross-table FD.**
All four variants use the **same** join order (`BIRTH_DEATH_GROWTH_RATES b JOIN COUNTRY_NAMES_AREA`);
the only real difference is whether the output `country_name` is read from `b` (BIRTH_DEATH…) or from
`c`/`a` (COUNTRY_NAMES_AREA). Those agree only when `country_code → country_name` holds **across the
two tables** — a data functional dependency, not a relational-algebra identity (same category as
`sf_bq280`). It is genuinely false without that fact, so we make it an explicit **hypothesis** (the
FD layer, `Operators/Constraints.lean`) and prove the rest: the `ON b.country_code = c.country_code`
restriction forces every joined row's two halves to share `country_code`, and the FD then forces the
two `country_name`s equal, so `SELECT b.country_name` ≡ `SELECT c.country_name` (`select_congr`).
Earlier triage mislabeled this as "join commutativity" — the join orders are in fact identical.

**Toolbox upshot.** A genuine *join-order swap* (`A JOIN B` ↔ `B JOIN A`), which other dataset
instances will need, requires **join commutativity** — previously missing. This work added it:
`swapAppend`, `crossProduct_comm`, `swapAppend_swapAppend`, `splitTuple_swapAppend`
(`Operators/CrossProduct.lean`) and `join_comm` (`Operators/Join.lean`). The theorem below
instantiates `join_comm` on these two tables to confirm it applies: swapping the join operands gives
the same rows up to the schema half-swap (`swapAppend`), for any join condition.
-/

namespace CrossSkill.Sf_bq060

/-- Full `BIRTH_DEATH_GROWTH_RATES` schema (8 columns) in the parser's canonical form. -/
abbrev BIRTH_DEATH_GROWTH_RATES : List SQLTypeProxy := [.string, .string, .int, .float, .float, .float, .float, .float]

-- column projections for BIRTH_DEATH_GROWTH_RATES
abbrev birth_death_growth_rates_country_code : TypedTupleOfList BIRTH_DEATH_GROWTH_RATES → String := fun t => t 0
abbrev birth_death_growth_rates_country_name : TypedTupleOfList BIRTH_DEATH_GROWTH_RATES → String := fun t => t 1
abbrev birth_death_growth_rates_year : TypedTupleOfList BIRTH_DEATH_GROWTH_RATES → Int := fun t => t 2
abbrev birth_death_growth_rates_crude_birth_rate : TypedTupleOfList BIRTH_DEATH_GROWTH_RATES → Rat := fun t => t 3
abbrev birth_death_growth_rates_crude_death_rate : TypedTupleOfList BIRTH_DEATH_GROWTH_RATES → Rat := fun t => t 4
abbrev birth_death_growth_rates_net_migration : TypedTupleOfList BIRTH_DEATH_GROWTH_RATES → Rat := fun t => t 5
abbrev birth_death_growth_rates_rate_natural_increase : TypedTupleOfList BIRTH_DEATH_GROWTH_RATES → Rat := fun t => t 6
abbrev birth_death_growth_rates_growth_rate : TypedTupleOfList BIRTH_DEATH_GROWTH_RATES → Rat := fun t => t 7

/-- Full `COUNTRY_NAMES_AREA` schema (3 columns) in the parser's canonical form. -/
abbrev COUNTRY_NAMES_AREA : List SQLTypeProxy := [.string, .string, .float]

-- column projections for COUNTRY_NAMES_AREA
abbrev country_names_area_country_code : TypedTupleOfList COUNTRY_NAMES_AREA → String := fun t => t 0
abbrev country_names_area_country_name : TypedTupleOfList COUNTRY_NAMES_AREA → String := fun t => t 1
abbrev country_names_area_country_area : TypedTupleOfList COUNTRY_NAMES_AREA → Rat := fun t => t 2

abbrev BDGR := BIRTH_DEATH_GROWTH_RATES
abbrev CNA  := COUNTRY_NAMES_AREA

/-- **join_comm demonstration** on this instance's two tables: swapping the join operands yields the
same row-set once the two schema halves are exchanged (`swapAppend`) and the condition is transported
through that swap. (Not the dataset's actual variant difference — see the header — but it confirms the
newly-added `join_comm` lemma instantiates here, which is what a real join-order rewrite would use.) -/
theorem join_order_swap (B : TypedRelationOfList BDGR) (C : TypedRelationOfList CNA)
    (cond : TypedTuple (Fin.append (colTypeOfList BDGR) (colTypeOfList CNA)) → Bool) :
    (join B C cond).rows.image swapAppend
      = (join C B (fun u => cond (swapAppend u))).rows :=
  join_comm B C cond

/-! ## The actual variant difference, IN-SCOPE under the cross-table FD

`BDGR b JOIN CNA c ON b.country_code=c.country_code`, `WHERE b.year=2017 AND c.country_area>500`.
Appended indices: `b` is the left half (0..7), `c` the right half (8..10): `b.country_code = t 0`,
`b.country_name = t 1`, `b.net_migration = t 5`, `c.country_code = t 8`, `c.country_name = t 9`,
`c.country_area = t 10`. Output schema `(country_name, net_migration)`. -/

/-- Common output schema `(country_name : String, net_migration : Rat)`. -/
abbrev OutCT : Fin 2 → Type := fun i => match i with | 0 => String | 1 => Rat
instance : ∀ i, DecidableEq (OutCT i) := fun i => match i with | 0 => inferInstance | 1 => inferInstance

/-- The appended `(BDGR ++ CNA)` schema. -/
abbrev appCT := Fin.append (colTypeOfList BDGR) (colTypeOfList CNA)

/-- The shared post-join relation, **abstracted**: `J` is whatever `BDGR ⋈ CNA` produces over the
appended schema. The join is *identical* on both variants, so we don't re-derive it (modelling it via
`join`/`crossProductRel` only makes the dependent term explode); we only apply the shared
`ON b.country_code=c.country_code AND WHERE year=2017 AND area>500`. -/
@[simp] def base (J : TypedRelation appCT) : TypedRelation appCT :=
  restriction
    (fun t => decide (t 0 = t 8) && decide (t 2 = (2017 : Int)) && decide ((500 : Rat) < t 10)) J

/-- `SELECT b.country_name, b.net_migration` (name from the BDGR half). -/
abbrev q_nameFromB (J : TypedRelation appCT) : TypedRelation OutCT :=
  select (colType := appCT) (outCT := OutCT)
    (fun _ => "") (fun t => fun j => match j with | 0 => t 1 | 1 => t 5) (base J)

/-- `SELECT c.country_name, b.net_migration` (name from the CNA half). -/
abbrev q_nameFromC (J : TypedRelation appCT) : TypedRelation OutCT :=
  select (colType := appCT) (outCT := OutCT)
    (fun _ => "") (fun t => fun j => match j with | 0 => t 9 | 1 => t 5) (base J)

/-- Under the **cross-table FD** `country_code → country_name` (as it manifests on joined rows:
matching `country_code` across the two halves ⇒ matching `country_name`), the two projections agree.
The `ON` restriction supplies the matching `country_code`; the FD then forces the names equal. -/
theorem equiv_of_FD (J : TypedRelation appCT)
    (hfd : ∀ t ∈ (base J).rows, t 0 = t 8 → t 1 = t 9) :
    q_nameFromB J = q_nameFromC J := by
  sql_equiv

/-! ## Edge 2 — alias-only (presentation), IN-SCOPE (pure algebra)

`semantic-probing` and `baseline-sg` both project `country_name` from `b`; they differ only in the
output column **aliases** (`AS "country_name"`, `AS "net_migration"` vs unaliased). An alias only
sets the result's label strings — the *row-set* of a `SELECT` is `image f` of the input, independent
of the labels — so the two variants return identical rows. (Distinct from edge 1, which is the
`b`-vs-`c` projection requiring the cross-table FD.) -/
theorem alias_only_same_rows (J : TypedRelation appCT) (l1 l2 : Fin 2 → String) :
    (select (colType := appCT) (outCT := OutCT) l1
        (fun t => fun j => match j with | 0 => t 1 | 1 => t 5) (base J)).rows
      = (select (colType := appCT) (outCT := OutCT) l2
        (fun t => fun j => match j with | 0 => t 1 | 1 => t 5) (base J)).rows := by
  sql_equiv

end CrossSkill.Sf_bq060
