import Mathlib
import LeanDatabase.TypedRelation

/-!
# Cross product (Cartesian product) of typed relations

`crossProductRel r1 r2` glues every pair of rows into a single tuple over the combined schema
`Fin.append colType1 colType2`. All the dependent-`Fin.append` plumbing — the `DecidableEq`/
`ToString` instances for the combined column family, the injectivity of tuple-gluing, and the
inverse `splitTuple` — lives here, so the join layer can stay schema-agnostic.
-/

namespace LeanDatabase

variable {n m : Nat}
variable {colType1 : Fin n → Type} [∀ i, DecidableEq (colType1 i)]
variable {colType2 : Fin m → Type} [∀ i, DecidableEq (colType2 i)]

-- Helper: Prove that the type (Fin.append t1 t2) i is definitionally equal
-- to the result of combining them.
omit [∀ i, DecidableEq (colType1 i)] [∀ i, DecidableEq (colType2 i)] in
theorem append_colType_eq (i : Fin (n + m)) :
  (Fin.append colType1 colType2 i) =
  (Fin.addCases colType1 colType2 i) := by
  simp only [Fin.append, Fin.addCases]

@[simp]
instance instDecidableEqAppend : ∀ i, DecidableEq (Fin.append colType1 colType2 i) := fun i =>
  Fin.addCases
    (fun i =>
      -- Left Case: Fin.append reduces to colType1
      have h : Fin.append colType1 colType2 (Fin.castAdd m i) = colType1 i := by simp [Fin.append, Fin.addCases]
      h ▸ inferInstance)
    (fun i =>
      -- Right Case: Fin.append reduces to colType2
      have h : Fin.append colType1 colType2 (Fin.natAdd n i) = colType2 i := by simp [Fin.append, Fin.addCases]
      h ▸ inferInstance)
    i

@[simp]
instance instToStringAppend {n m : Nat}
    {colType1 : Fin n → Type} [∀ i, ToString (colType1 i)]
    {colType2 : Fin m → Type} [∀ i, ToString (colType2 i)] :
    ∀ i, ToString (Fin.append colType1 colType2 i) := fun i =>
  Fin.addCases
    (fun i =>
      have h : Fin.append colType1 colType2 (Fin.castAdd m i) = colType1 i := by simp [Fin.append, Fin.addCases]
      h ▸ inferInstance)
    (fun i =>
      have h : Fin.append colType1 colType2 (Fin.natAdd n i) = colType2 i := by simp [Fin.append, Fin.addCases]
      h ▸ inferInstance)
    i

/-
## Cross Product
Note: we rename labels if they are same bases on given aliases prefix
-/

@[simp, grind .]
def crossProductRel (r1 : TypedRelation colType1) (r2 : TypedRelation colType2) (table1_alias: String := "L") (table2_alias: String := "R") :
    TypedRelation (Fin.append colType1 colType2) :=

  -- Check if labels are not same, then prefixLabel them
  let l1_list := List.ofFn r1.labels
  let l2_list := List.ofFn r2.labels

  let hasCollision := l1_list.any (fun label => l2_list.contains label)

  let l1_labels := if hasCollision then (prefixLabels table1_alias r1).labels else r1.labels
  let l2_labels := if hasCollision then (prefixLabels table2_alias r2).labels else r2.labels

  {
    -- Combine the determined labels
    labels := Fin.append l1_labels l2_labels,

    -- Combine Rows (Cartesian Product)
    rows := (r1.rows ×ˢ r2.rows).image (fun (pair : TypedTuple colType1 × TypedTuple colType2) =>
       fun i =>
         Fin.addCases
           (fun i =>
             -- PROOF 1: The complex type equals the simple type
             have h : Fin.append colType1 colType2 (Fin.castAdd m i) = colType1 i := by simp [Fin.append, Fin.addCases]
             -- REWRITE: Cast 'pair.1 i' (simple) to the complex type
             h.symm ▸ pair.1 i)
           (fun i =>
             -- PROOF 2: The complex type equals the simple type
             have h : Fin.append colType1 colType2 (Fin.natAdd n i) = colType2 i := by simp [Fin.append, Fin.addCases]
             -- REWRITE: Cast 'pair.2 i' (simple) to the complex type
             h.symm ▸ pair.2 i)
           i
      )
  }

-- Helper Lemma: Injectivity of Tuple Combination
-- Proves that gluing two tuples together preserves unique data.
omit [∀ i, DecidableEq (colType1 i)] [∀ i, DecidableEq (colType2 i)] in
@[simp]
theorem combine_tuples_injective :
  Function.Injective (fun (pair : TypedTuple colType1 × TypedTuple colType2) =>
       fun i =>
         (Fin.addCases
           (fun i =>
             have h : Fin.append colType1 colType2 (Fin.castAdd m i) = colType1 i := by simp [Fin.append, Fin.addCases]
             h.symm ▸ pair.1 i)
           (fun i =>
             have h : Fin.append colType1 colType2 (Fin.natAdd n i) = colType2 i := by simp [Fin.append, Fin.addCases]
             h.symm ▸ pair.2 i)
           i : Fin.append colType1 colType2 i)
       ) := by
  intro (a1, b1) (a2, b2) h_eq
  simp only at h_eq
  ext i
  · have h_left := congr_fun h_eq (Fin.castAdd m i)
    simp_all only [Fin.addCases_left]
    grind
  · have h_right := congr_fun h_eq (Fin.natAdd n i)
    simp_all only [Fin.addCases_right]
    grind


-- Theorem: Cardinality of Cross Product
-- |R1 × R2| = |R1| * |R2|
-- "The size of the product is the product of the sizes"
theorem crossProduct_card (r1 : TypedRelation colType1) (r2 : TypedRelation colType2)
    (a1 a2 : String) :
    (crossProductRel r1 r2 a1 a2).rows.card = r1.rows.card * r2.rows.card := by
  simp_all only [crossProductRel, List.contains_eq_mem, List.mem_ofFn, List.any_eq_true,
    decide_eq_true_eq, exists_exists_eq_and, prefixLabels]
  rw [Finset.card_image_of_injective]
  · simp only [Finset.card_product]
  · simp only [combine_tuples_injective]


-- Theorem: Zero Propagation (Left)
-- ∅ × R2 = ∅
-- "Crossing with an empty table yields an empty table"
theorem crossProduct_empty_left (r1 : TypedRelation colType1) (r2 : TypedRelation colType2)
    (a1 a2 : String) (h : r1.rows = ∅) :
    (crossProductRel r1 r2 a1 a2).rows = ∅ := by
  simp only [crossProductRel, h]
  grind

-- Theorem: Zero Propagation (Right)
-- R1 × ∅ = ∅
-- "Crossing with an empty table yields an empty table"
theorem crossProduct_empty_right (r1 : TypedRelation colType1) (r2 : TypedRelation colType2)
    (a1 a2 : String) (h : r2.rows = ∅) :
    (crossProductRel r1 r2 a1 a2).rows = ∅ := by
  simp only [crossProductRel, h]
  grind


-- Helper: Split Tuple
-- Needed for the Membership theorem. Deconstructs a big tuple back into two small ones.
@[simp, grind .]
def splitTuple (t : TypedTuple (Fin.append colType1 colType2)) :
    TypedTuple colType1 × TypedTuple colType2 :=
  (
    fun i =>
      have h : Fin.append colType1 colType2 (Fin.castAdd m i) = colType1 i := by simp [Fin.append, Fin.addCases]
      h ▸ t (Fin.castAdd m i),
    fun i =>
      have h : Fin.append colType1 colType2 (Fin.natAdd n i) = colType2 i := by simp [Fin.append, Fin.addCases]
      h ▸ t (Fin.natAdd n i)
  )

-- Theorem: Membership of Cross Product
-- t ∈ (R1 × R2) ↔ t_left ∈ R1 ∧ t_right ∈ R2
-- "A row is in the product if and only if its parts are in the source tables"
theorem mem_crossProduct (r1 : TypedRelation colType1) (r2 : TypedRelation colType2)
    (a1 a2 : String) (t : TypedTuple (Fin.append colType1 colType2)) :
    t ∈ (crossProductRel r1 r2 a1 a2).rows ↔
    (splitTuple t).1 ∈ r1.rows ∧ (splitTuple t).2 ∈ r2.rows := by

  simp only [crossProductRel, Finset.mem_image]
  constructor
  -- Forward (If t is in result, its parts are in R1 and R2)
  · intro h
    rcases h with ⟨p, h_mem, h_eq⟩
    -- The pair p comes from the product R1 × R2
    rw [Finset.mem_product] at h_mem
    rcases h_mem with ⟨h_left, h_right⟩

    -- We know t = combine(p). We substitute this into the goal.
    subst h_eq
    simp_all only [splitTuple, Fin.addCases_left, Fin.addCases_right]
    constructor
    · convert h_left
      grind
    · convert h_right
      grind

  -- Backward (If parts are in R1 and R2, their combination is t)
  · simp_all only [splitTuple, Finset.mem_product, Prod.exists]
    intro h
    use (splitTuple t).1, (splitTuple t).2
    constructor
    · assumption
    · ext i
      induction i using Fin.addCases
      · simp_all only [Fin.addCases_left]
        grind
      · simp_all only [Fin.addCases_right]
        grind

end LeanDatabase
