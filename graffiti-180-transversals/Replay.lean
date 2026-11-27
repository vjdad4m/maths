import Lean.Replay
import Lean.Util.Path

open Lean

def main (args : List String) : IO Unit := do
  let [file, theoremName] := args | throw (IO.userError "expected module and theorem")
  initSearchPath (← findSysroot)
  let (mod, _region) ← readModuleData file
  let base ← importModules mod.imports {} 0
  let goal := theoremName.toName
  if base.contains goal then throw (IO.userError "theorem already present before replay")
  let mut decls : Std.HashMap Name ConstantInfo := ∅
  for c in mod.constants do
    if c.isUnsafe || c.isPartial || c.isAxiom then throw (IO.userError s!"inadmissible declaration {c.name}")
    decls := decls.insert c.name c
  let checked ← base.replay decls
  let some (.thmInfo _) := checked.find? goal | throw (IO.userError "expected theorem absent")
  IO.println s!"Kernel replay accepted {decls.size} declarations including {goal}."
