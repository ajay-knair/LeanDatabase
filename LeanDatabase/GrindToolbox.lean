import LeanDatabase.RelationalAlgebra
import LeanDatabase.TypedAggregation

/-!
# Grind toolbox — database identities registered with `grind`

Importing this module turns a curated, *confluent* set of relational-algebra identities into
oriented `grind` rewrites, so downstream query-equivalence theorems over `TypedRelation` close
with a bare `grind +locals`. (The aggregation lemmas — grouping, `COUNT`/`SUM` coalesce, group
membership/max — are already registered in `LeanDatabase.TypedAggregation`, re-exported here.)

Everything tagged `@[grind =]` is an oriented, terminating rewrite — no commutativity /
associativity (those would loop), and no two rules sharing a left-hand side.
-/

namespace LeanDatabase

attribute [grind =]
  restriction_idempotence          -- σ_p(σ_p R) = σ_p R
  inter_idempotence                -- R ∩ R = R
  union_absorb_inter               -- R ∪ (R ∩ S) = R
  inter_absorb_union               -- R ∩ (R ∪ S) = R
  diff_empty                       -- R − ∅ = R
  union_identity                   -- R ∪ ∅ = R
  restriction_inter_distrib        -- σ_p(R ∩ S) = σ_p R ∩ σ_p S
  restriction_diff_distrib         -- σ_p(R − S) = σ_p R − σ_p S

end LeanDatabase
