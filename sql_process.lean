import Lean.Meta
import LeanDatabase.Parser
open Lean Meta LeanDatabase

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false


partial def process_loop (env: Environment)(getLine : Unit →  IO String) (putStrLn : String → IO Unit) : IO UInt32 := do
  IO.eprintln "Ready to process equivalence checks."
  let inp ← getLine ()
  if inp.trimAscii.toString.isEmpty then
    process_loop env getLine putStrLn
  else
  match Json.parse inp with
  | Except.error e =>
    let output := Json.mkObj [("status", Json.str "error"), ("message", Json.str s!"Failed to parse JSON: {e}")]
    IO.println output.compress
    process_loop env getLine putStrLn
  | Except.ok js =>
    IO.eprintln s!"Received JSON: {js.pretty}"
    IO.eprintln "Checking equivalence..."
    let ctx: Core.Context := {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 0, maxRecDepth := 1000000}
    let core := checkEquivCore js
    let result? := core.run' ctx {env := env}
    let result? ←  result?.toIO'
    IO.eprintln "Equivalence check completed."
    match result? with
    | Except.error e =>
      let output := Json.mkObj [("status", Json.str "error"), ("message", Json.str s!"Error during equivalence check: {← e.toMessageData.toString}")]
      IO.println output.compress
    | Except.ok isEquivalent =>
      let output := Json.mkObj [("status", Json.str "ok"), ("equivalent", Json.bool isEquivalent)]
      IO.println output.compress
    process_loop env getLine putStrLn

unsafe def main (_ : List String) : IO UInt32 := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ←
    importModules (loadExts := true) #[
    {module := `Mathlib},
    {module:= `LeanDatabase.Parser},
    {module:= `LeanDatabase.GrindToolbox},
    {module:= `LeanDatabase}] {}
  let stdin ←  IO.getStdin
  let stdout ← IO.getStdout
  let getLine : Unit → IO String := fun _ => stdin.getLine
  let putStrLn : String → IO Unit := fun s => do
    stdout.putStrLn s
    stdout.flush
  process_loop env getLine putStrLn
