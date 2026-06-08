import LeanDatabase.TypedRelation
open Lean

namespace LeanDatabase

/- ## SQL Column Def-/

structure BaseColumnDef where
  name : String
  sqltype: String
deriving Repr, Inhabited, BEq, ToJson, FromJson

structure ColumnDef extends BaseColumnDef where
  isPrimaryKey : Bool := false
  isNullable : Bool := true
  isUnique : Bool := false
  defaultValue : Option String := none
deriving Repr, Inhabited, BEq, ToJson, FromJson

/- ## Table Schema built upon TypedRelation -/

structure TableSchema (n : Nat) where
  tableName : String
  columns : List ColumnDef
  columnIndex: String -> Option (Fin n)
deriving Inhabited

/-! ## Enhanced TypedRelation with Schema -/

structure TypedTableRelation (colType : Fin n → Type)[(i : Fin n) → DecidableEq (colType i)] where
  schema : TableSchema n
  relation : TypedRelation colType
  -- Invariant: schema.columns.length = n
deriving Inhabited

namespace SqlDsl

/-! ## SQL DSL-/

inductive SQLType where
  | INT
  | VARCHAR (maxLen : Nat)
  | BOOL
  | FLOAT
  | TEXT
deriving Repr, DecidableEq

def SQLType.toLeanType : SQLType → Type
  | SQLType.INT => Int
  | SQLType.VARCHAR _ => String
  | SQLType.BOOL => Bool
  | SQLType.FLOAT => Float
  | SQLType.TEXT => String

instance : ToString SQLType where
  toString
    | SQLType.INT => "INT"
    | SQLType.VARCHAR maxLen => s!"VARCHAR({maxLen})"
    | SQLType.BOOL => "BOOL"
    | SQLType.FLOAT => "FLOAT"
    | SQLType.TEXT => "TEXT"

/-! ## Column Constraint -/

structure ColConstraint where
  primaryKey : Bool := false
  notNull : Bool := false
  unique : Bool := false
  default : Option String := none
deriving Repr, BEq

/-! ## SQL Column Definition (Parser-friendly) -/

structure SQLColumn where
  name : String
  sqlType : SQLType
  constraints : ColConstraint := {}
deriving Repr, BEq

/-! ## SQL CREATE TABLE Statement -/

structure CreateTableStmt where
  tableName : String
  columns : List SQLColumn
deriving Repr, BEq

/-! ## Helper: Convert SQLColumn to ColumnDef -/

def SQLColumn.toColumnDef (col : SQLColumn) : ColumnDef :=
  {
    name := col.name,
    sqltype := s!"{col.sqlType}",
    isPrimaryKey := col.constraints.primaryKey,
    isNullable := !col.constraints.notNull,
    isUnique := col.constraints.unique,
    defaultValue := col.constraints.default
  }

/-! ## Helper to create a table from a simple list of columns -/


end SqlDsl

end LeanDatabase
