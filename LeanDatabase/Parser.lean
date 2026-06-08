import Lean

open Lean Meta Elab Term

namespace LeanDatabase

def elabFilter (schema : List (Name × Name)) (stx : Syntax) : TermElabM Expr := do
  match schema with
  | [] => elabTerm stx none
  | (name, colType) :: rest => do
    let colTypeExpr ←  Term.mkConst colType
    withLocalDeclD name colTypeExpr fun localVar => do
      let restExpr ← elabFilter rest stx
      mkLambdaFVars #[localVar] restExpr

def parseFilter (schemaStr : List (String × String)) (str : String) : TermElabM Expr := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term str | throwError "Failed to parse filter expression: {str}"
  let schema := schemaStr.map (fun (name, colType) => (name.toName, colType.toName))
  elabFilter schema stx

def egFilter := parseFilter [("age", "Int"), ("isActive", "Bool")] "age > 30 && isActive"

elab "egfilter%" : term => do
  let e ← egFilter
  return e

#check egfilter%

#eval egfilter% 32 true

example : egfilter% = fun age isActive ↦ (30 < age) && isActive  := by
  grind

end LeanDatabase
