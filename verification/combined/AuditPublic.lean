module

public import Solution

@[expose] public section

/-! Inspect all merged proof roots and the actual imported modules. -/

#check TuranUniversality.Registry.main_theorem
#print axioms TuranUniversality.Registry.main_theorem
#check TuranUniversality.Registry.numerical_main_theorem
#print axioms TuranUniversality.Registry.numerical_main_theorem
#check TuranUniversality.Registry.structural_main_theorem
#print axioms TuranUniversality.Registry.structural_main_theorem

open Lean Elab Command in
run_elab do
  let env ← getEnv
  let imports := env.header.modules.map fun i => Json.mkObj [
    ("module", toJson i.module.toString),
    ("importAll", toJson i.importAll),
    ("isExported", toJson i.isExported),
    ("isMeta", toJson i.isMeta),
    ("hasData", toJson i.hasData)]
  liftM <| IO.FS.writeFile "verification/combined/public-import-closure.json" (Json.arr imports).pretty
