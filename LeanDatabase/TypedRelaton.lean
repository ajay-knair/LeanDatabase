namespace LeanDatabase

abbrev TypedTuple {n : Nat} (types : Fin n → Type) := (i : Fin n) → types i

def TypedRelation {n : Nat} (types : Fin n → Type) := List (TypedTuple types)

def projection {n m : Nat} (types : Fin n → Type) (indices : Fin m → Fin n) (rel : TypedRelation types) :
    TypedRelation (fun j => types (indices j)) :=
  rel.map (fun tuple j => tuple (indices j))

end LeanDatabase
