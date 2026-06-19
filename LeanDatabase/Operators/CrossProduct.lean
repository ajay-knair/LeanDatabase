import Mathlib
import LeanDatabase.TypedRelation

/-!
# Cross product (Cartesian product) of typed relations

`crossProductRel r1 r2` glues every pair of rows into a single tuple over the combined schema
`Fin.append colType1 colType2`. All the dependent-`Fin.append` plumbing — the `DecidableEq`/
`ToString` instances for the combined column family, the injectivity of tuple-gluing, and the
inverse `splitTuple` — lives here, so the join layer can stay schema-agnostic.

The column names will be full names like `table1.age` and `table2.age` hence no clashing of labels will occur.
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
def crossProductRel (r1 : TypedRelation colType1) (r2 : TypedRelation colType2) :
    TypedRelation (Fin.append colType1 colType2) :=

  -- Check if labels are not same, then prefixLabel them
  let l1_list := List.ofFn r1.labels
  let l2_list := List.ofFn r2.labels

  let hasCollision := l1_list.any (fun label => l2_list.contains label)

  {
    -- Combine the determined labels
    labels := Fin.append r1.labels r2.labels

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
theorem crossProduct_card (r1 : TypedRelation colType1) (r2 : TypedRelation colType2):
    (crossProductRel r1 r2).rows.card = r1.rows.card * r2.rows.card := by
  simp_all only [crossProductRel]
  rw [Finset.card_image_of_injective]
  · simp only [Finset.card_product]
  · simp only [combine_tuples_injective]


-- Theorem: Zero Propagation (Left)
-- ∅ × R2 = ∅
-- "Crossing with an empty table yields an empty table"
theorem crossProduct_empty_left (r1 : TypedRelation colType1) (r2 : TypedRelation colType2) (h : r1.rows = ∅) :
    (crossProductRel r1 r2).rows = ∅ := by
  simp only [crossProductRel, h]
  grind

-- Theorem: Zero Propagation (Right)
-- R1 × ∅ = ∅
-- "Crossing with an empty table yields an empty table"
theorem crossProduct_empty_right (r1 : TypedRelation colType1) (r2 : TypedRelation colType2)  (h : r2.rows = ∅) :
    (crossProductRel r1 r2).rows = ∅ := by
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

-- Helper: Combine Tuple — the inverse of `splitTuple`. Glues a `(left, right)` pair into one
-- appended-schema tuple (the named form of the gluing used inside `crossProductRel`).
def combineTuple (p : TypedTuple colType1 × TypedTuple colType2) :
    TypedTuple (Fin.append colType1 colType2) :=
  fun i =>
    Fin.addCases
      (fun i =>
        have h : Fin.append colType1 colType2 (Fin.castAdd m i) = colType1 i := by simp [Fin.append, Fin.addCases]
        h.symm ▸ p.1 i)
      (fun i =>
        have h : Fin.append colType1 colType2 (Fin.natAdd n i) = colType2 i := by simp [Fin.append, Fin.addCases]
        h.symm ▸ p.2 i)
      i

-- Splitting a combined tuple recovers the original pair (`splitTuple ∘ combineTuple = id`).
omit [∀ i, DecidableEq (colType1 i)] [∀ i, DecidableEq (colType2 i)] in
@[simp] theorem splitTuple_combineTuple (p : TypedTuple colType1 × TypedTuple colType2) :
    splitTuple (combineTuple p) = p := by
  apply Prod.ext
  · funext k
    simp only [splitTuple, combineTuple, Fin.addCases_left]
    grind
  · funext k
    simp only [splitTuple, combineTuple, Fin.addCases_right]
    grind

-- Theorem: Membership of Cross Product
-- t ∈ (R1 × R2) ↔ t_left ∈ R1 ∧ t_right ∈ R2
-- "A row is in the product if and only if its parts are in the source tables"
theorem mem_crossProduct (r1 : TypedRelation colType1) (r2 : TypedRelation colType2)
  (t : TypedTuple (Fin.append colType1 colType2)) :
    t ∈ (crossProductRel r1 r2).rows ↔
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

/-
## Cross-product commutativity (up to the schema half-swap)

`crossProductRel r1 r2` lives over `Fin.append colType1 colType2`, while `crossProductRel r2 r1`
lives over `Fin.append colType2 colType1` — *different* dependent schemas. `swapAppend` is the
reindexing that exchanges the two halves; under it the two cross products have the same row-set.
-/

-- Swap the two halves of an appended-schema tuple: `(c1 ++ c2)`-tuple ↦ `(c2 ++ c1)`-tuple.
@[simp]
def swapAppend (t : TypedTuple (Fin.append colType1 colType2)) :
    TypedTuple (Fin.append colType2 colType1) :=
  fun j =>
    Fin.addCases
      (fun (j : Fin m) =>
        have h : Fin.append colType2 colType1 (Fin.castAdd n j) = colType2 j := by
          simp [Fin.append, Fin.addCases]
        h.symm ▸ (splitTuple t).2 j)
      (fun (j : Fin n) =>
        have h : Fin.append colType2 colType1 (Fin.natAdd m j) = colType1 j := by
          simp [Fin.append, Fin.addCases]
        h.symm ▸ (splitTuple t).1 j)
      j

-- Splitting a swapped tuple just swaps the two component tuples.
omit [∀ i, DecidableEq (colType1 i)] [∀ i, DecidableEq (colType2 i)] in
theorem splitTuple_swapAppend (t : TypedTuple (Fin.append colType1 colType2)) :
    splitTuple (swapAppend t) = ((splitTuple t).2, (splitTuple t).1) := by
  apply Prod.ext
  · funext k
    simp only [splitTuple, swapAppend, Fin.addCases_left]
    grind
  · funext k
    simp only [splitTuple, swapAppend, Fin.addCases_right]
    grind

-- `swapAppend` is an involution (swapping back recovers the original tuple).
omit [∀ i, DecidableEq (colType1 i)] [∀ i, DecidableEq (colType2 i)] in
theorem swapAppend_swapAppend (t : TypedTuple (Fin.append colType1 colType2)) :
    swapAppend (swapAppend t) = t := by
  funext j
  induction j using Fin.addCases with
  | left k => simp only [swapAppend, splitTuple, Fin.addCases_left, Fin.addCases_right]; grind
  | right k => simp only [swapAppend, splitTuple, Fin.addCases_left, Fin.addCases_right]; grind

-- **Cross-product commutativity.** The two argument orders have the same row-set up to `swapAppend`.
theorem crossProduct_comm (r1 : TypedRelation colType1) (r2 : TypedRelation colType2) :
    (crossProductRel r1 r2).rows.image swapAppend = (crossProductRel r2 r1).rows := by
  ext u
  simp only [Finset.mem_image]
  rw [mem_crossProduct]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [mem_crossProduct] at ht
    rw [splitTuple_swapAppend]
    exact ⟨ht.2, ht.1⟩
  · rintro ⟨h1, h2⟩
    refine ⟨swapAppend u, ?_, swapAppend_swapAppend u⟩
    rw [mem_crossProduct, splitTuple_swapAppend]
    exact ⟨h2, h1⟩

-- Combining a split tuple recovers the original (`combineTuple ∘ splitTuple = id`).
omit [∀ i, DecidableEq (colType1 i)] [∀ i, DecidableEq (colType2 i)] in
@[simp] theorem combineTuple_splitTuple (t : TypedTuple (Fin.append colType1 colType2)) :
    combineTuple (splitTuple t) = t := by
  funext j
  induction j using Fin.addCases with
  | left k => simp only [combineTuple, splitTuple, Fin.addCases_left]; grind
  | right k => simp only [combineTuple, splitTuple, Fin.addCases_right]; grind

/-
## Cross-product associativity (up to the schema re-bracketing)

`(c1 ++ c2) ++ c3` vs `c1 ++ (c2 ++ c3)` — `assocAppend` re-brackets, built purely from
`splitTuple`/`combineTuple`. Under it the two nestings of the cross product have the same row-set.
This is the data core of three-way join associativity.
-/
variable {p : Nat} {colType3 : Fin p → Type} [∀ i, DecidableEq (colType3 i)]

-- Re-bracket `((c1 ++ c2) ++ c3)`-tuple to `(c1 ++ (c2 ++ c3))`-tuple.
def assocAppend (t : TypedTuple (Fin.append (Fin.append colType1 colType2) colType3)) :
    TypedTuple (Fin.append colType1 (Fin.append colType2 colType3)) :=
  combineTuple ((splitTuple (splitTuple t).1).1,
                combineTuple ((splitTuple (splitTuple t).1).2, (splitTuple t).2))

-- **Cross-product associativity.** Left- and right-nested cross products agree up to `assocAppend`.
theorem crossProduct_assoc (r1 : TypedRelation colType1) (r2 : TypedRelation colType2)
    (r3 : TypedRelation colType3) :
    (crossProductRel (crossProductRel r1 r2) r3).rows.image assocAppend
      = (crossProductRel r1 (crossProductRel r2 r3)).rows := by
  ext u
  simp only [Finset.mem_image, mem_crossProduct]
  constructor
  · rintro ⟨t, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
    simp only [assocAppend, splitTuple_combineTuple]
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨combineTuple (combineTuple ((splitTuple u).1, (splitTuple (splitTuple u).2).1),
            (splitTuple (splitTuple u).2).2), ?_, ?_⟩
    · simp only [splitTuple_combineTuple]; exact ⟨⟨h1, h2⟩, h3⟩
    · simp only [assocAppend, splitTuple_combineTuple, Prod.mk.eta, combineTuple_splitTuple]

end LeanDatabase
