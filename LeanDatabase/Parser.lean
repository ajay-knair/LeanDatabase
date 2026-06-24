import LeanDatabase.Parser.Types
import LeanDatabase.Parser.Syntax
import LeanDatabase.Parser.Context
import LeanDatabase.Parser.Query
import LeanDatabase.SQLEquiv

/-!
# SQL → `TypedRelation` parser

Aggregates the parser modules and exposes the public API. The pipeline:

* `Parser.Types`   — SQL type reification (`SQLTypeProxy`) and list-indexed schemas.
* `Parser.Syntax`  — the `sql_query` / `sql_from` surface syntax and `JOIN` desugaring.
* `Parser.Context` — column-binding elaboration context + per-operator (algebra) elaborators.
* `Parser.Query`   — `elabSqlQuery` and the `parse*` entry points.

The `checkEquiv` API below parses two `WHERE`-predicate strings and asks `sql_equiv` whether they are
equal — the entry point used by the `sql_process` executable.
-/

open Lean Meta Elab Term

namespace LeanDatabase

/-- Parse the `first`/`second` filter strings from a JSON record (with its `schema`) and report
whether `sql_equiv` proves them equal. -/
def checkEquivSimple (data: Json) : TermElabM Bool := do
    let .ok schema := data.getObjValAs? (List Json) "schema" | throwError "Missing schema"
    let schemaStr : List (String × String) ←  schema.mapM fun colJson => do
      let .ok name := colJson.getObjValAs? String "name" | throwError "Missing column name"
      let .ok sqlType := colJson.getObjValAs? String "type" | throwError "Missing column type"
      pure (name, sqlType)
    let .ok firstStr := data.getObjValAs? String "first" | throwError "Missing first expression"
    let .ok secondStr := data.getObjValAs? String "second" | throwError "Missing second expression"
    let firstExpr ← parseTypedTupleFilter schemaStr firstStr
    let secondExpr ← parseTypedTupleFilter schemaStr secondStr
    let goalType ←  mkEq firstExpr secondExpr
    let mvar ← mkFreshExprMVar goalType
    let tac ← `(tacticSeq| sql_equiv)
    try
        let (goals, _) ← Elab.runTactic mvar.mvarId! tac
        pure goals.isEmpty
    catch _ =>
        pure false

def checkEquivSimpleCore (data: Json) : CoreM Bool := do
    let res :=  checkEquivSimple data |>.run' {} |>.run' {}
    res

def dataEg := json% {"schema": [{"name": "age", "type": "Int"}, {"name": "isActive", "type": "Bool"}],
  "first": "SELECT * FROM table WHERE age > 30 AND isActive","second": "SELECT * FROM table WHERE age > 30 && isActive && age > 20"}

-- #eval checkEquiv dataEg

end LeanDatabase
