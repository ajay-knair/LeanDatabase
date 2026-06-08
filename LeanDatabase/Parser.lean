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

example : egfilter% = fun age isActive ↦ (31 ≤  age) && isActive && (20 < age)  := by
  grind

def egFilter' := parseFilter [("age", "Int"), ("isActive", "Bool")] "age > 30"

elab "egfilter%%" : term => do
  let e ← egFilter'
  return e

#check egfilter%%

#eval egfilter%% 32 true

def checkEquiv (data: Json) : TermElabM Bool := do
    let .ok schema := data.getObjValAs? (List Json) "schema" | throwError "Missing schema"
    let schemaStr : List (String × String) ←  schema.mapM fun colJson => do
      let .ok name := colJson.getObjValAs? String "name" | throwError "Missing column name"
      let .ok sqlType := colJson.getObjValAs? String "type" | throwError "Missing column type"
      pure (name, sqlType)
    let .ok firstStr := data.getObjValAs? String "first" | throwError "Missing first expression"
    let .ok secondStr := data.getObjValAs? String "second" | throwError "Missing second expression"
    let firstExpr ← parseFilter schemaStr firstStr
    let secondExpr ← parseFilter schemaStr secondStr
    let goalType ←  mkEq firstExpr secondExpr
    logInfo m!"Checking equivalence of:\n  {firstStr}\n  {secondStr}\nParsed as:\n  {← ppExpr firstExpr}\n  {← ppExpr secondExpr}; Goal: {← ppExpr goalType}"
    let mvar ← mkFreshExprMVar goalType
    let tac ← `(tacticSeq| grind)
    try
        let (goals, _) ← Elab.runTactic mvar.mvarId! tac
        pure goals.isEmpty
    catch e =>
        logInfo m!"Error occurred while running tactic: {e.toMessageData}"
        pure false

def checkEquivCore (data: Json) : CoreM Bool := do
    let res :=  checkEquiv data |>.run' {} |>.run' {}
    res

macro "SELECT" " * " "FROM" ident "WHERE" t:term : term =>
    return t

def dataEg := json% {
  "schema": [
    {"name": "age", "type": "Int"},
    {"name": "isActive", "type": "Bool"}
  ],
  "first": "SELECT * FROM table WHERE age > 30 && isActive",
  "second": "SELECT * FROM table WHERE age > 30 && isActive && age > 20"
}

#eval checkEquiv dataEg

end LeanDatabase
