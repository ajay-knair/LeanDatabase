import LeanDatabase.RelationalAlgebra

/-!
# Example 10 — `OR` predicate ≡ `UNION` ≡ disjoint `UNION ALL`

Three ways to write "tickets that are open or high priority", all equivalent. This is a
*set-semantics* fact: `UNION` deduplicates, and `OR` over a set returns each matching row
once — so we model it with the `Finset`-based `TypedRelation` (not bags). The third form makes
the two branches disjoint (`priority='high' AND status<>'open'`) so even `UNION ALL` produces
no duplicates.

## The three SQL queries being proved equivalent

```sql
-- query_Or:
SELECT * FROM tickets WHERE status = 'open' OR priority = 'high';

-- query_Union:
SELECT * FROM tickets WHERE status = 'open'
UNION
SELECT * FROM tickets WHERE priority = 'high';

-- query_UnionAll: branches made disjoint, so UNION ALL is safe
SELECT * FROM tickets WHERE status = 'open'
UNION ALL
SELECT * FROM tickets WHERE priority = 'high' AND status <> 'open';
```
-/

namespace Example10
open LeanDatabase

variable {n : Nat}
variable {colType : Fin n → Type} [∀ i, DecidableEq (colType i)]
set_option linter.unusedSectionVars false

variable (isOpen : TypedTuple colType → Bool)
variable (isHigh : TypedTuple colType → Bool)

/-- `SELECT * FROM tickets WHERE status='open' OR priority='high'`. -/
def query_Or (tickets : TypedRelation colType) : TypedRelation colType :=
  restriction (pOr isOpen isHigh) tickets

/-- `(WHERE status='open') UNION (WHERE priority='high')`. -/
def query_Union (tickets : TypedRelation colType) : TypedRelation colType :=
  union (restriction isOpen tickets) (restriction isHigh tickets)

/-- `(WHERE status='open') UNION ALL (WHERE priority='high' AND status<>'open')`. -/
def query_UnionAll (tickets : TypedRelation colType) : TypedRelation colType :=
  union (restriction isOpen tickets) (restriction (pAnd isHigh (pNot isOpen)) tickets)

theorem query_equivalence (tickets : TypedRelation colType) :
    query_Or isOpen isHigh tickets = query_Union isOpen isHigh tickets ∧
    query_Or isOpen isHigh tickets = query_UnionAll isOpen isHigh tickets := by
  sql_equiv

end Example10
