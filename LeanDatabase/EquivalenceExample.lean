import LeanDatabase.RelationalAlgebra

namespace QueryOptimization
open LeanDatabase

variable {n : Nat}
variable {types : Fin n → Type} [∀ i, DecidableEq (types i)]

/-!
### Scenario 1: The "MapReduce" Optimization
(Distributivity of Selection over Union)
-/

-- The Predicate: "Is this a High Value row?"
variable (isHighValue : TypedTuple types → Bool)

-- 1. The "Naive" Query (Bottleneck)
-- "Union everything first, then filter."
def query_Slow (r1 r2 : TypedRelation types) : TypedRelation types :=
  restriction isHighValue (union r1 r2)

-- 2. The "Optimized" Query (Parallelizable)
-- "Filter locally first, then union results."
def query_Fast (r1 r2 : TypedRelation types) : TypedRelation types :=
  union (restriction isHighValue r1) (restriction isHighValue r2)

-- 3. THE PROOF
-- We prove that no matter what data is in r1 or r2, the result is identical.
theorem mapReduce_equivalence (r1 r2 : TypedRelation types) :
    query_Slow isHighValue r1 r2 = query_Fast isHighValue r1 r2 := by
  grind [query_Slow, query_Fast]

/-!
### Scenario 2: The "Index Merge" Optimization
(Cascading Selection)
-/

-- Predicates: "Is Active?" and "Is High Value?"
variable (isActive : TypedTuple types → Bool)

-- 1. The "Naive" Query (Two passes over data)
-- "Filter for Active, write result. Read result, filter for HighValue."
def query_MultiPass (r : TypedRelation types) : TypedRelation types :=
  restriction isHighValue (restriction isActive r)

-- 2. The "Optimized" Query (Single pass / Index Seek)
-- "Check both conditions at once."
def query_SinglePass (r : TypedRelation types) : TypedRelation types :=
  restriction (fun t => isHighValue t && isActive t) r

-- 3. THE PROOF
omit [∀ i, DecidableEq (types i)] in
theorem pipeline_equivalence (r : TypedRelation types) :
    query_MultiPass isHighValue isActive r = query_SinglePass isHighValue isActive r := by
  grind [query_MultiPass, query_SinglePass]
  -- We used theorem proved previously

/-! ### Scenario 3: -/

-- "Is this user Active?"
variable (isActive : TypedTuple types → Bool)
-- "Is this user Banned?"
variable (isBanned : TypedTuple types → Bool)

-- The "Messy" Query
-- ( (Active(A) ∪ Active(B)) - Banned(A ∪ B) )
-- "Combine active users, then remove anyone who appears in the global banned list."
def query_Messy (tableA tableB : TypedRelation types) : TypedRelation types :=
  minus
    (union (restriction isActive tableA) (restriction isActive tableB))
    (restriction isBanned (union tableA tableB))

-- The "Optimized" Query
-- σ_{Active ∧ ¬Banned} (A ∪ B)
-- "Union first, then check both conditions in one pass."
def query_Clean (tableA tableB : TypedRelation types) : TypedRelation types :=
  restriction (fun t => isActive t && !isBanned t) (union tableA tableB)

theorem complex_query_equivalence (tableA tableB : TypedRelation types) :
    query_Messy isActive isBanned tableA tableB =
    query_Clean isActive isBanned tableA tableB := by
  grind [query_Messy, query_Clean]

end QueryOptimization
