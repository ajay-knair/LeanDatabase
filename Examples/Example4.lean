import LeanDatabase.RelationalAlgebra

/-!
# Example 4 — Combine + global anti-set ≡ single combined predicate

Take active users from two tables, then remove anyone in the global banned set; this equals
unioning the two tables and keeping rows that are active and not banned in one pass.

## The two SQL queries being proved equivalent

```sql
-- query_Messy: (active(A) ∪ active(B)) minus banned(A ∪ B)
(SELECT * FROM tableA WHERE is_active
 UNION
 SELECT * FROM tableB WHERE is_active)
EXCEPT
SELECT * FROM (SELECT * FROM tableA UNION SELECT * FROM tableB) WHERE is_banned;

-- query_Clean: union first, then one combined predicate
SELECT * FROM (SELECT * FROM tableA UNION SELECT * FROM tableB)
WHERE is_active AND NOT is_banned;
```
-/

namespace Example4
open LeanDatabase

variable {n : Nat}
variable {colType : Fin n → Type} [∀ i, DecidableEq (colType i)]
set_option linter.unusedSectionVars false

variable (isActive : TypedTuple colType → Bool)
variable (isBanned : TypedTuple colType → Bool)

/-- `(active(A) ∪ active(B)) − banned(A ∪ B)`. -/
def query_Messy (tableA tableB : TypedRelation colType) : TypedRelation colType :=
  minus
    (union (restriction isActive tableA) (restriction isActive tableB))
    (restriction isBanned (union tableA tableB))

/-- `σ_{active ∧ ¬banned} (A ∪ B)`. -/
def query_Clean (tableA tableB : TypedRelation colType) : TypedRelation colType :=
  restriction (fun t => isActive t && !isBanned t) (union tableA tableB)

theorem query_equivalence (tableA tableB : TypedRelation colType) :
    query_Messy isActive isBanned tableA tableB =
    query_Clean isActive isBanned tableA tableB := by
  sql_equiv

end Example4
