import LeanDatabase.Parser
open LeanDatabase

/-!
# Example 0 — Ten warm-up query-pair equivalences (all within the `Parser/Query.lean` surface)

Each item below is **two distinct SQL queries** — both expressible by the parser in
`LeanDatabase/Parser/Query.lean` (`SELECT … FROM … WHERE …`, comma / `JOIN … ON`, `AND`/`OR`/`NOT`,
`DISTINCT`, `ORDER BY`, `LIMIT`, and subqueries-in-`FROM`) — modelled in the relational algebra and
proved equal with `sql_equiv`. They are the small, real rewrites a query planner performs; a good
first read before the larger `Example1`…`Example21`.

Two fixed schemas are reused throughout:

* `users(id : Nat, age : Int, active : Bool)`
* `orders(uid : Nat, total : Int)`
-/

namespace Example0

abbrev usersCT  : Fin 3 → Type := fun i => match i with | 0 => Nat | 1 => Int | 2 => Bool
abbrev ordersCT : Fin 2 → Type := fun i => match i with | 0 => Nat | 1 => Int
instance : ∀ i, DecidableEq (usersCT i)  := fun i => match i with | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance
instance : ∀ i, DecidableEq (ordersCT i) := fun i => match i with | 0 => inferInstance | 1 => inferInstance

/-! Column accessors (named like the SQL columns) for `users`. -/
abbrev u_id     : TypedTuple usersCT → Nat  := fun t => t 0
abbrev u_age    : TypedTuple usersCT → Int  := fun t => t 1
abbrev u_active : TypedTuple usersCT → Bool := fun t => t 2

/-! ===================================================================================
## 1. Pushing one of two `AND`-ed filters into a subquery (selection cascade)
```sql
-- query_OnePass
SELECT * FROM users WHERE age > 18 AND active;

-- query_Subquery
SELECT * FROM (SELECT * FROM users WHERE age > 18) AS u WHERE u.active;
```
=================================================================================== -/

def q01_OnePass (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction (fun t => decide (u_age t > 18) && u_active t) users

def q01_Subquery (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction u_active (restriction (fun t => decide (u_age t > 18)) users)

theorem eg01 (users : TypedRelation usersCT) :
    q01_OnePass users = q01_Subquery users := by sql_equiv

/-! ===================================================================================
## 2. `WHERE` conjuncts may be reordered (the optimiser is free to pick the cheaper one first)
```sql
SELECT * FROM users WHERE age > 18 AND active;
SELECT * FROM users WHERE active AND age > 18;
```
=================================================================================== -/

def q02_AgeFirst (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction (fun t => decide (u_age t > 18) && u_active t) users

def q02_ActiveFirst (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction (fun t => u_active t && decide (u_age t > 18)) users

theorem eg02 (users : TypedRelation usersCT) :
    q02_AgeFirst users = q02_ActiveFirst users := by sql_equiv

/-! ===================================================================================
## 3. A redundant `DISTINCT` can be dropped (set semantics — rows are already a set)
```sql
SELECT DISTINCT * FROM users WHERE active;
SELECT          * FROM users WHERE active;
```
=================================================================================== -/

def q03_Distinct (users : TypedRelation usersCT) : TypedRelation usersCT :=
  distinct (restriction u_active users)

def q03_Plain (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction u_active users

theorem eg03 (users : TypedRelation usersCT) :
    q03_Distinct users = q03_Plain users := by sql_equiv

/-! ===================================================================================
## 4. `ORDER BY … LIMIT` does not change the *set* of rows returned
```sql
SELECT * FROM users WHERE active ORDER BY age DESC LIMIT 50;
SELECT * FROM users WHERE active;
```
=================================================================================== -/

def q04_OrderLimit (users : TypedRelation usersCT) : TypedRelation usersCT :=
  limit 50 (orderBy u_age (restriction u_active users))

def q04_Plain (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction u_active users

theorem eg04 (users : TypedRelation usersCT) :
    q04_OrderLimit users = q04_Plain users := by sql_equiv

/-! ===================================================================================
## 5. De Morgan on a `WHERE` predicate
```sql
SELECT * FROM users WHERE NOT (age > 18 OR active);
SELECT * FROM users WHERE NOT (age > 18) AND NOT active;
```
=================================================================================== -/

def q05_NotOr (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction (fun t => !(decide (u_age t > 18) || u_active t)) users

def q05_AndNot (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction (fun t => !decide (u_age t > 18) && !u_active t) users

theorem eg05 (users : TypedRelation usersCT) :
    q05_NotOr users = q05_AndNot users := by sql_equiv

/-! ===================================================================================
## 6. An explicit `JOIN … ON` is the comma-product plus the `ON` condition in `WHERE`
(exactly the desugaring `Parser/Syntax.lean`'s `escapeJoin` performs)
```sql
SELECT * FROM users JOIN orders ON users.id = orders.uid;
SELECT * FROM users, orders WHERE users.id = orders.uid;
```
=================================================================================== -/

abbrev joinCT := Fin.append usersCT ordersCT
/-- On the appended schema, `users.id = t 0`, `orders.uid = t 3`. -/
abbrev onCond : TypedTuple joinCT → Bool := fun t => decide (t 0 = t 3)

def q06_Join (users : TypedRelation usersCT) (orders : TypedRelation ordersCT) :
    TypedRelation joinCT :=
  restriction onCond (crossProductRel users orders)

def q06_CommaWhere (users : TypedRelation usersCT) (orders : TypedRelation ordersCT) :
    TypedRelation joinCT :=
  restriction onCond (crossProductRel users orders)

theorem eg06 (users : TypedRelation usersCT) (orders : TypedRelation ordersCT) :
    q06_Join users orders = q06_CommaWhere users orders := by sql_equiv

/-! ===================================================================================
## 7. A repeated `AND` conjunct is idempotent
```sql
SELECT * FROM users WHERE active AND active;
SELECT * FROM users WHERE active;
```
=================================================================================== -/

def q07_Twice (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction (fun t => u_active t && u_active t) users

def q07_Once (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction u_active users

theorem eg07 (users : TypedRelation usersCT) :
    q07_Twice users = q07_Once users := by sql_equiv

/-! ===================================================================================
## 8. Double negation in `WHERE`
```sql
SELECT * FROM users WHERE NOT (NOT active);
SELECT * FROM users WHERE active;
```
=================================================================================== -/

def q08_DoubleNeg (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction (fun t => !(!u_active t)) users

def q08_Plain (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction u_active users

theorem eg08 (users : TypedRelation usersCT) :
    q08_DoubleNeg users = q08_Plain users := by sql_equiv

/-! ===================================================================================
## 9. Absorption: `p OR (p AND q)` simplifies to `p`
```sql
SELECT * FROM users WHERE active OR (active AND age > 18);
SELECT * FROM users WHERE active;
```
=================================================================================== -/

def q09_Absorb (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction (fun t => u_active t || (u_active t && decide (u_age t > 18))) users

def q09_Plain (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction u_active users

theorem eg09 (users : TypedRelation usersCT) :
    q09_Absorb users = q09_Plain users := by sql_equiv

/-! ===================================================================================
## 10. `DISTINCT` commutes with `WHERE` (both are set-level operations)
```sql
SELECT DISTINCT * FROM users WHERE active;
SELECT * FROM (SELECT DISTINCT * FROM users) AS u WHERE u.active;
```
=================================================================================== -/

def q10_DistinctThenWhere (users : TypedRelation usersCT) : TypedRelation usersCT :=
  distinct (restriction u_active users)

def q10_WhereThenDistinct (users : TypedRelation usersCT) : TypedRelation usersCT :=
  restriction u_active (distinct users)

theorem eg10 (users : TypedRelation usersCT) :
    q10_DistinctThenWhere users = q10_WhereThenDistinct users := by sql_equiv

end Example0
