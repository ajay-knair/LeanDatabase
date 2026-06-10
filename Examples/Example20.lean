import LeanDatabase.SQLEquiv
open LeanDatabase

/-!
# Example 20 — three "boss" rewrites: big, multi-clause SQL proved by a bare `sql_equiv`

Where Examples 1–19 each isolate one identity, this file stress-tests the toolbox on **large,
realistic optimizer rewrites** — the kind an autoconverter would emit from a SQL benchmark. Every
predicate is built from the **named combinators** (`between`/`inList`/`colGe`/`colEq`), every
table-op from the **named operators** (`union`/`minus`/`semijoin`/`projection`/`distinct` and the
`okeys`/`cnt` aggregates) — there is no raw `decide` anywhere. All three close with `sql_equiv`.

A single shared "orders" schema is used throughout:

| index | 0    | 1      | 2      | 3   | 4      |
|-------|------|--------|--------|-----|--------|
| field | id   | amount | region | age | status |
| type  | Nat  | Nat    | String | Nat | String |
-/

namespace Example20

abbrev OrdCT : Fin 5 → Type := fun i =>
  match i with | 0 => Nat | 1 => Nat | 2 => String | 3 => Nat | 4 => String
instance : ∀ i, DecidableEq (OrdCT i) := fun i =>
  match i with | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance
                | 3 => inferInstance | 4 => inferInstance

abbrev idP   : TypedTuple OrdCT → Nat    := fun t => t 0
abbrev amtP  : TypedTuple OrdCT → Nat    := fun t => t 1
abbrev regP  : TypedTuple OrdCT → String := fun t => t 2
abbrev ageP  : TypedTuple OrdCT → Nat    := fun t => t 3
abbrev statP : TypedTuple OrdCT → String := fun t => t 4

/-- The recurring "eligible customer" filter:
    `amount BETWEEN 100 AND 1000 AND region IN ('US','EU','APAC') AND age >= 18`.
    Three different combinators (`between`, `inList`, `colGe`) over three different columns. -/
abbrev eligible : TypedTuple OrdCT → Bool := fun t =>
  between amtP 100 1000 t && inList regP ["US", "EU", "APAC"] t && colGe ageP 18 t

/-- `status = 'banned'`. -/
abbrev banned : TypedTuple OrdCT → Bool := colEq statP "banned"

/-! ## Example 1 — predicate pushdown through a 3-way `UNION` and an `EXCEPT`

```sql
-- messy: filter each source, union, then subtract the globally-banned rows; finally project.
SELECT DISTINCT id, region, amount FROM (
      ( SELECT * FROM archive  WHERE <eligible>
        UNION
        SELECT * FROM live     WHERE <eligible>
        UNION
        SELECT * FROM partners WHERE <eligible> )
    EXCEPT
      SELECT * FROM (archive UNION live UNION partners) WHERE status = 'banned' )

-- clean: union first, then one combined WHERE.
SELECT DISTINCT id, region, amount
FROM (archive UNION live UNION partners)
WHERE <eligible> AND NOT status = 'banned';
```

**Why they're equal.** This is the multi-table generalization of Example 4. `sql_equiv` pushes the
selection through the union (`restriction_union_distrib`), turns `(σ_e X) EXCEPT (σ_b X)` into the
single predicate `σ_{e ∧ ¬b} X` (`restriction_diff_conj_restriction`), and finally pushes the
shared `projection`/`DISTINCT` over the now-identical relations. The `projection` and `distinct`
wrappers are set-semantics no-ops on top. -/
abbrev pickCols : Fin 3 → Fin 5 := ![0, 2, 1]   -- SELECT id, region, amount

/-- Filter-then-union-then-except, projected `DISTINCT`. -/
@[simp] def messy (archive live partners : TypedRelation OrdCT) :=
  distinct (projection pickCols (
    minus
      (union (union (restriction eligible archive) (restriction eligible live))
             (restriction eligible partners))
      (restriction banned (union (union archive live) partners))))

/-- Union-then-one-combined-filter, projected `DISTINCT`. -/
@[simp] def clean (archive live partners : TypedRelation OrdCT) :=
  distinct (projection pickCols (
    restriction (fun t => eligible t && !banned t) (union (union archive live) partners)))

theorem equiv (archive live partners : TypedRelation OrdCT) :
    messy archive live partners = clean archive live partners := by
  sql_equiv

/-! ## Example 2 — partition collapse + `WHERE` pushdown through a semi-join (`EXISTS`)

```sql
-- split: the same EXISTS query, with the (banned / not-banned) cases written as two UNION branches.
SELECT DISTINCT * FROM (
      ( SELECT * FROM orders o
        WHERE <eligible> AND status = 'banned'
          AND EXISTS (SELECT 1 FROM vip v WHERE v.id = o.id) )
    UNION
      ( SELECT * FROM orders o
        WHERE <eligible> AND NOT status = 'banned'
          AND EXISTS (SELECT 1 FROM vip v WHERE v.id = o.id) ) )

-- pushed: drop the redundant case split and push <eligible> below the semi-join.
SELECT DISTINCT * FROM orders o
WHERE <eligible> AND EXISTS (SELECT 1 FROM vip v WHERE v.id = o.id);
```

**Why they're equal.** Two independent rewrites compose. First, `σ_{e∧banned}(X) ∪ σ_{e∧¬banned}(X)`
collapses to `σ_e(X)` — the excluded-middle partition on `banned` (a row is in exactly one branch).
Second, a `WHERE` on a semi-join migrates onto its left input: `σ_e(orders ⋉ vip) = (σ_e orders) ⋉
vip`, because a semi-join *is* a `restriction`, so this is just selection commuting/cascading
(`restriction_cascade`). `DISTINCT` is a no-op on top. -/
abbrev VipCT : Fin 1 → Type := fun _ => Nat            -- vip(id)
instance : ∀ i, DecidableEq (VipCT i) := fun _ => inferInstance

/-- `EXISTS (SELECT 1 FROM vip v WHERE v.id = o.id)` — the semi-join correlation on `id`. -/
abbrev existsVip (o : TypedTuple OrdCT) (v : TypedTuple VipCT) : Bool := decide (idP o = v 0)

/-- The redundant two-branch (`banned` / `NOT banned`) form. -/
@[simp] def split (orders : TypedRelation OrdCT) (V : TypedRelation VipCT) :=
  distinct (union
    (restriction (fun t => eligible t && banned t)  (semijoin orders V existsVip))
    (restriction (fun t => eligible t && !banned t) (semijoin orders V existsVip)))

/-- The collapsed form with the filter pushed below the semi-join. -/
@[simp] def pushed (orders : TypedRelation OrdCT) (V : TypedRelation VipCT) :=
  distinct (semijoin (restriction eligible orders) V existsVip)

theorem equiv2 (orders : TypedRelation OrdCT) (V : TypedRelation VipCT) :
    split orders V = pushed orders V := by
  sql_equiv

/-! ## Example 3 — the `GROUP BY` total over a filtered `UNION`

```sql
-- Sum each group's COUNT(*) back up...
SELECT SUM(c) FROM (
    SELECT region, COUNT(*) AS c
    FROM (archive UNION live)
    WHERE <eligible>
    GROUP BY region ) g
-- ...equals the ungrouped COUNT(*) of the same filtered table.
SELECT COUNT(*) FROM (archive UNION live) WHERE <eligible>;
```

**Why they're equal.** Summing the per-group counts over every present group key is just the
fiberwise partition of the rows by `region`: `∑_{k ∈ okeys} cnt(k) = COUNT(*)`
(`sum_cnt_okeys_eq_relCount`). It holds for any base relation, here the filtered union. -/
theorem equiv3 (archive live : TypedRelation OrdCT) :
    (∑ k ∈ okeys regP (restriction eligible (union archive live)),
        cnt regP k (restriction eligible (union archive live)))
      = relCount (restriction eligible (union archive live)) := by
  sql_equiv

end Example20
