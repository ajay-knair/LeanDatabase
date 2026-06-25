import LeanDatabase.Parser
open LeanDatabase

/-!
# Example 0 — Ten warm-up query-pair equivalences (all within the `Parser/Query.lean` surface)

Each item below is **two distinct SQL queries** — both expressible by the parser in
`LeanDatabase/Parser/Query.lean` (`SELECT … FROM … WHERE …`, comma / `JOIN … ON`, `AND`/`OR`/`NOT`,
`DISTINCT`, `ORDER BY`, `LIMIT`, and subqueries-in-`FROM`) — modelled in the relational algebra and
proved equal with `sql_equiv`. They are the small, real rewrites a query planner performs; a good
first read before the larger `Example1`…`Example21`.

Two fixed schemas are used:

* `users(id : Nat, age : Int, active : Bool)`
* `orders(uid : Nat, total : Int)`
-/

namespace Example0

abbrev usersCT  : Fin 3 → Type := fun i => match i with | 0 => Nat | 1 => Int | 2 => Bool
abbrev ordersCT : Fin 2 → Type := fun i => match i with | 0 => Nat | 1 => Int
instance : ∀ i, DecidableEq (usersCT i)  := fun i => match i with | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance
instance : ∀ i, DecidableEq (ordersCT i) := fun i => match i with | 0 => inferInstance | 1 => inferInstance

set_option linter.unusedSectionVars false

/- `p`, `q` stand for the `WHERE` predicates (e.g. `age > 18`, `active`); `k` for an `ORDER BY` key. -/
variable (p q : TypedTuple usersCT → Bool) {K : Type} (k : TypedTuple usersCT → K)

/-! ===================================================================================
## 1. Pushing one of two `AND`-ed filters into a subquery (selection cascade)
```sql
-- query_OnePass
SELECT * FROM users WHERE p AND q;

-- query_Subquery
SELECT * FROM (SELECT * FROM users WHERE p) AS u WHERE u.q;
```
=================================================================================== -/

@[simp, grind]
def q01_OnePass (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction (fun t => p t && q t) users

@[simp, grind]
def q01_Subquery (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction q (restriction p users)

theorem eg01 (users : TypedRelation usersCT) :
    q01_OnePass p q users = q01_Subquery p q users := by
  sql_equiv

/-! ===================================================================================
## 2. `WHERE` conjuncts may be reordered (the optimiser is free to pick the cheaper one first)
```sql
SELECT * FROM users WHERE p AND q;
SELECT * FROM users WHERE q AND p;
```
=================================================================================== -/

def q02_PFirst (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction (fun t => p t && q t) users

def q02_QFirst (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction (fun t => q t && p t) users

theorem eg02 (users : TypedRelation usersCT) :
    q02_PFirst p q users = q02_QFirst p q users := by sql_equiv

/-! ===================================================================================
## 3. A redundant `DISTINCT` can be dropped (set semantics — rows are already a set)
```sql
SELECT DISTINCT * FROM users WHERE p;
SELECT          * FROM users WHERE p;
```
=================================================================================== -/

def q03_Distinct (users : TypedRelation usersCT) : TypedRelation usersCT :=
  distinct (restriction p users)

def q03_Plain (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction p users

theorem eg03 (users : TypedRelation usersCT) :
    q03_Distinct p users = q03_Plain p users := by sql_equiv

/-! ===================================================================================
## 4. `ORDER BY … LIMIT` does not change the *set* of rows returned
```sql
SELECT * FROM users WHERE p ORDER BY k DESC LIMIT 50;
SELECT * FROM users WHERE p;
```
=================================================================================== -/

def q04_OrderLimit (users : TypedRelation usersCT) : TypedRelation usersCT :=
  limit 50 (orderBy k (restriction p users))

def q04_Plain (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction p users

theorem eg04 (users : TypedRelation usersCT) :
    q04_OrderLimit p k users = q04_Plain p users := by sql_equiv

/-! ===================================================================================
## 5. De Morgan on a `WHERE` predicate
```sql
SELECT * FROM users WHERE NOT (p OR q);
SELECT * FROM users WHERE NOT p AND NOT q;
```
=================================================================================== -/

def q05_NotOr (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction (fun t => !(p t || q t)) users

def q05_AndNot (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction (fun t => !p t && !q t) users

theorem eg05 (users : TypedRelation usersCT) :
    q05_NotOr p q users = q05_AndNot p q users := by sql_equiv

/-! ===================================================================================
## 6. An explicit `JOIN … ON` is the comma-product plus the `ON` condition in `WHERE`
(exactly the desugaring `Parser/Syntax.lean`'s `escapeJoin` performs)
```sql
SELECT * FROM users JOIN orders ON users.id = orders.uid;
SELECT * FROM users, orders WHERE users.id = orders.uid;
```
=================================================================================== -/

abbrev joinCT := Fin.append usersCT ordersCT

/-- `c` stands for the `ON` / `WHERE` condition over the joined schema (e.g. `users.id = orders.uid`). -/
def q06_Join (c : TypedTuple joinCT → Bool) (users : TypedRelation usersCT) (orders : TypedRelation ordersCT) :
    TypedRelation joinCT :=
  restriction c (crossProductRel users orders)

def q06_CommaWhere (c : TypedTuple joinCT → Bool) (users : TypedRelation usersCT) (orders : TypedRelation ordersCT) :
    TypedRelation joinCT :=
  restriction c (crossProductRel users orders)

theorem eg06 (c : TypedTuple joinCT → Bool) (users : TypedRelation usersCT) (orders : TypedRelation ordersCT) :
    q06_Join c users orders = q06_CommaWhere c users orders := by sql_equiv

/-! ===================================================================================
## 7. A repeated `AND` conjunct is idempotent
```sql
SELECT * FROM users WHERE p AND p;
SELECT * FROM users WHERE p;
```
=================================================================================== -/

def q07_Twice (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction (fun t => p t && p t) users

def q07_Once (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction p users

theorem eg07 (users : TypedRelation usersCT) :
    q07_Twice p users = q07_Once p users := by sql_equiv

/-! ===================================================================================
## 8. Double negation in `WHERE`
```sql
SELECT * FROM users WHERE NOT (NOT p);
SELECT * FROM users WHERE p;
```
=================================================================================== -/

def q08_DoubleNeg (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction (fun t => !(!p t)) users

def q08_Plain (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction p users

theorem eg08 (users : TypedRelation usersCT) :
    q08_DoubleNeg p users = q08_Plain p users := by sql_equiv

/-! ===================================================================================
## 9. Absorption: `p OR (p AND q)` simplifies to `p`
```sql
SELECT * FROM users WHERE p OR (p AND q);
SELECT * FROM users WHERE p;
```
=================================================================================== -/

def q09_Absorb (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction (fun t => p t || (p t && q t)) users

def q09_Plain (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction p users

theorem eg09 (users : TypedRelation usersCT) :
    q09_Absorb p q users = q09_Plain p users := by sql_equiv

/-! ===================================================================================
## 10. `DISTINCT` commutes with `WHERE` (both are set-level operations)
```sql
SELECT DISTINCT * FROM users WHERE p;
SELECT * FROM (SELECT DISTINCT * FROM users) AS u WHERE u.p;
```
=================================================================================== -/

def q10_DistinctThenWhere (users : TypedRelation usersCT) : TypedRelation usersCT :=
  distinct (restriction p users)

def q10_WhereThenDistinct (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction p (distinct users)

theorem eg10 (users : TypedRelation usersCT) :
    q10_DistinctThenWhere p users = q10_WhereThenDistinct p users := by sql_equiv

end Example0
