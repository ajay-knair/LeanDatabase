import Mathlib
import LeanDatabase.Parser.Types
import LeanDatabase.TypedRelation

open Lean
namespace LeanDatabase

variable {k: List Nat}

abbrev colTypes (k: List Nat) := (i : Fin k.length) -> Fin (k[i]) → Type

def schemaLengths (schemas : List (Name × List (Name × SQLTypeProxy))): List Nat := schemas.map (fun (_, b) => b.length)

def getColTypes (l: List (Name × SQLTypeProxy)) : Fin l.length → Type :=
  fun i => (l.get i).snd.type

instance getColTypesDecEq (l: List (Name × SQLTypeProxy)) : (i : Fin l.length) → DecidableEq (getColTypes l i) := by
  match l with
  | [] =>
    intro ⟨i, hi⟩
    simp at hi
  | t :: rest =>
    intro ⟨i, hi⟩
    match i with
    | 0 => rw [getColTypes]; exact inferInstance
    | j+1 =>
      exact getColTypesDecEq rest ⟨j, by simp at hi; assumption⟩

def colTypesfromSchema (schemas : List (Name × List (Name × SQLTypeProxy))) : colTypes (schemaLengths schemas) :=
  fun i j =>
    have h_i : i.val < schemas.length := by
      have hi := i.isLt
      simp [schemaLengths] at hi
      exact hi
    let schema := schemas.get ⟨i.val, h_i⟩
    have h_j : j.val < schema.snd.length := by
      have hj := j.isLt
      simp [schemaLengths] at hj
      grind
    getColTypes schema.snd ⟨j.val, h_j⟩

instance {schemas} (i j) :
    DecidableEq (colTypesfromSchema schemas i j) := by
  unfold colTypesfromSchema getColTypes
  infer_instance

def mergeColTypes : (k : List Nat) → colTypes k → Fin (k.sum) → Type
  | [], _, x => x.elim0
  | hd :: tl, f, x =>
    if h : x.val < hd then
      f ⟨0, by simp⟩ ⟨x.val, h⟩
    else
      let fTail : colTypes tl := fun i j => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ j
      mergeColTypes tl fTail ⟨x.val - hd, by grind⟩

instance mergeColTypesDecEq :
    (k : List Nat) → (cols : colTypes k) →
    [(i : Fin k.length) → (j : Fin k[i]) → DecidableEq (cols i j)] →
    (x : Fin k.sum) → DecidableEq (mergeColTypes k cols x)
  | [], _, _, x => x.elim0
  | hd :: tl, cols, hdec, x => by
      unfold mergeColTypes
      split
      · rename_i h
        exact hdec ⟨0, by simp⟩ ⟨x.val, h⟩
      · exact @mergeColTypesDecEq tl
          (fun i j => cols ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ j)
          (fun i j => hdec ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ j)
          ⟨x.val - hd, by grind⟩

def injection : (k : List Nat) → (i : Fin k.length) → Fin (k.get i) → Fin (k.sum)
  | [], i, _ => i.elim0
  | hd :: tl, ⟨0, _⟩, j =>
    ⟨j.val, by grind⟩
  | hd :: tl, ⟨m + 1, h⟩, j =>
    let g := injection tl ⟨m, Nat.le_of_succ_le_succ h⟩ j
    ⟨hd + g.val, by grind⟩

theorem merge_comp_injection {k : List Nat} (f : colTypes k) (i : Fin k.length) (j : Fin (k.get i)) :
    mergeColTypes k f (injection k i j) = f i j := by
      revert j; induction' k with hd tl ih <;> simp +decide [ * ] at *;
      · fin_cases i;
      · rcases i with ⟨ _ | i, hi ⟩ <;> simp_all +decide [ injection ];
        · unfold mergeColTypes; aesop;
        · convert ih ( fun i j => f ⟨ i.val + 1, Nat.succ_lt_succ i.isLt ⟩ j ) ⟨ i, by simpa using hi ⟩ using 1;
          simp +decide [ mergeColTypes ]



def egSchemas : List (Name × List (Name × SQLTypeProxy)) := [
  (`Users, [(`id, .int), (`username, .string)]),
  (`Posts, [(`is_published, .bool)])
]

def egMyColTypes := colTypesfromSchema egSchemas
def egFlatTypes := mergeColTypes (schemaLengths egSchemas) egMyColTypes

def crossProd (schemas : List (Name × List (Name × SQLTypeProxy))) :=
  let namesProd := schemas.flatMap (fun (a , b) => (b.map (fun (x,y)=> x.toString)))
  have h: (schemaLengths schemas).sum = namesProd.length := by simp [namesProd, schemaLengths]
  let rel : (TypedRelation (mergeColTypes (schemaLengths schemas) (colTypesfromSchema schemas))) :=
  {
    labels := fun i => namesProd.get (Fin.cast h i),
    rows := ∅
  }
  rel

--#check crossProd egSchemas

def projns (schemas : List (Name × List (Name × SQLTypeProxy))) :=
  let colTypesOfSchemas := colTypesfromSchema schemas
  fun (i : Fin (schemas.length)) =>
    projection (injection (schemaLengths schemas) ⟨i, by simp[schemaLengths]⟩) (crossProd schemas)

--#check projns egSchemas





/-
** Obsolete Code **

def crossProductType (schemas : List (Name × List (Name × SQLTypeProxy))) : Type :=
  let flatTypeList := schemas.flatMap (fun (_ ,b) => (b.map (fun (_,y) => y)))
  let typeList := schemas.map (fun (_ ,b) => (b.map (fun (_,y) => y)))
  let crossProductType := TypedRelationOfList flatTypeList
  let projectionMapTypes := typeList.map (fun a => (crossProductType → TypedRelationOfList a))
  projectionMapTypes.foldl (fun acc x => acc × x) crossProductType


#reduce crossProductType [(`a, [(`x, SQLTypeProxy.int), (`y, SQLTypeProxy.bool)]),(`b, [(`x', SQLTypeProxy.string), (`y', SQLTypeProxy.bool)])]

-- We want to assert that passing an empty schema list
-- results exactly in `TypedRelationOfList []`
example : crossProductType [] = TypedRelationOfList [] := by
  rfl

-- Another test asserting a specific output structure for a specific input
example : crossProductType [(`T1, [(`C1, .int)])] =
  (TypedRelationOfList [.int] × (TypedRelationOfList [.int] → TypedRelationOfList [.int])) := by
  rfl

example :
  crossProductType [
    (`T1, [(`C1, .int)]),
    (`T2, [(`C2, .string), (`C3, .int)]),
    (`T3, [])
  ]
  =
  -- Notice the heavy left-nesting (((Init × Proj1) × Proj2) × Proj3)
  ( ( ( TypedRelationOfList [.int, .string, .int]
        ×
        -- Proj1 (T1)
        (TypedRelationOfList [.int, .string, .int] → TypedRelationOfList [.int])
      )
      ×
      -- Proj2 (T2)
      (TypedRelationOfList [.int, .string, .int] → TypedRelationOfList [.string, .int])
    )
    ×
    -- Proj3 (T3 - Empty)
    (TypedRelationOfList [.int, .string, .int] → TypedRelationOfList [])
  )
:= by rfl

def typedTupleTuples (schemas : List (Name × List (Name × SQLTypeProxy))) :=
  let colTypesOfSchemas := colTypesfromSchema schemas
  fun (i : Fin (schemas.length + 1)) =>
    match i with
    | ⟨0, _⟩ =>
      TypedRelation (mergeColTypes (schemaLengths schemas) colTypesOfSchemas)
    | ⟨j + 1, hj⟩ =>
      have h_lt : j < schemas.length := Nat.lt_of_succ_lt_succ hj
      TypedRelation (colTypesOfSchemas ⟨j, by simp[h_lt, schemaLengths]⟩)
-/


end LeanDatabase
