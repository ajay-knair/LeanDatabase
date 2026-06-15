import Lean
import Mathlib
import LeanDatabase.Schema
import LeanDatabase.SQLToolbox
import LeanDatabase.Parser

open Lean Meta Elab Term

namespace LeanDatabase

namespace archive

def withColumnVars (schemaName: Name) (schema : List (Name × SQLTypeProxy))  (k : α →  TermElabM Expr) (x : α) : TermElabM Expr := do
  match schema with
  | [] => k x
  | (name, colType) :: rest => do
    let colTypeExpr := typeExpr colType
    let fullName := schemaName ++ name
    withLocalDeclD fullName colTypeExpr fun localVar => do
      withLetDecl name colTypeExpr localVar fun localVar' => do
        let restExpr ← withColumnVars schemaName rest k x
        mkLambdaFVars #[localVar] <| ← mkLetFVars #[localVar'] restExpr


def withSchemasVars (schemas : List (Name × List (Name × SQLTypeProxy))) (k : α →  TermElabM Expr) (x : α) : TermElabM Expr := do
  match schemas with
  | [] => k x
  | (schemaName, schema) :: rest => do
    let colTypes := schema.map (fun (_, colType) => colType)
    let listExpr ← sqlTypeListExpr colTypes
    let type ← mkAppM ``TypedRelationOfList #[listExpr]
    withLocalDeclD schemaName type fun typedTuple => do
      let inner ← withColumnVars schemaName schema (fun x => withSchemasVars rest k x) x
      mkLambdaFVars #[typedTuple] inner


def elabFilter (schemas : List (Name × List (Name × SQLTypeProxy))) (stx : Syntax)  : TermElabM Expr := do
    withSchemasVars schemas (fun stx => elabTermEnsuringType stx (mkConst ``Bool)) stx


def parseFilter (schemaStr : List (String × String)) (str : String) : TermElabM Expr := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term str | throwError "Failed to parse filter expression: {str}"
  let schema := schemaStr.map (fun (name, colType) => (name.toName, sqlProxy colType))
  elabFilter [(`schema, schema)] stx



def egFilter := parseFilter [("age", "Int"), ("isActive", "Bool")] "age > 30 && isActive"


-- #check egTypedTupleMap

elab "egfilter%" : term => do
  let e ← egFilter
  return e

example : egfilter% = fun _ age isActive ↦ (31 ≤  age) && isActive && (20 < age)  := by
  grind

def egFilter' := parseFilter [("age", "Int"), ("isActive", "Bool")] "age > 30"


elab "egfilter%%" : term => do
  let e ← egFilter'
  return e

end archive

end LeanDatabase
