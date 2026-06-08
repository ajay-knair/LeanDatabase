import Lean
import LeanDatabase.Schema

open Lean Meta Elab Term

namespace LeanDatabase

/--
# Parser for SQL-like filter expressions

Since SQL types are all Lean constants, we represent them by names.
-/
def elabFilter (schema : List (Name × Name)) (stx : Syntax) : TermElabM Expr := do
  match schema with
  | [] => elabTermEnsuringType stx (mkConst ``Bool)
  | (name, colType) :: rest => do
    let colTypeExpr ←  Term.mkConst colType
    withLocalDeclD name colTypeExpr fun localVar => do
      let restExpr ← elabFilter rest stx
      mkLambdaFVars #[localVar] restExpr

def normalizeSQLType (sqlType : String) : String :=
  let s := sqlType.toLower
  if s.startsWith "varchar" then "String"
  else if s.startsWith "int" then "Int"
  else if s.startsWith "bool" then "Bool"
  else if s.startsWith "float" then "Float"
  else if s.startsWith "text" then "String"
  else if s.startsWith "char" then "String"
  else s

def parseFilter (schemaStr : List (String × String)) (str : String) : TermElabM Expr := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term str | throwError "Failed to parse filter expression: {str}"
  let schema := schemaStr.map (fun (name, colType) => (name.toName, (normalizeSQLType colType).toName))
  elabFilter schema stx

def egFilter := parseFilter [("age", "Int"), ("isActive", "Bool")] "age > 30 && isActive"

elab "egfilter%" : term => do
  let e ← egFilter
  return e

#check egfilter%

#eval egfilter% 32 true

example : egfilter% = fun age isActive ↦ (30 < age) && isActive  := by
  grind

def egFilter' := parseFilter [("age", "Int"), ("isActive", "Bool")] "age > 30"

elab "egfilter%%" : term => do
  let e ← egFilter'
  return e

#check egfilter%%

#eval egfilter%% 32 true


end LeanDatabase
