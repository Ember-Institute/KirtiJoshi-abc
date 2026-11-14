import Lean
import Theorems.Thm_AbcAdaptation_Tripod_epsilonELargeHeight
open Lean
run_meta do
  let env ← getEnv
  let mut out : Array Json := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some m := env.header.moduleNames[idx.toNat]? | continue
    unless m == `Theorems.Thm_AbcAdaptation_Tripod_epsilonELargeHeight do continue
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do throwError "Unapproved axiom {ax} in {name}"
    out := out.push (Json.mkObj [("name", toJson name.toString), ("axioms", toJson (axs.map toString))])
  IO.FS.writeFile ".local/adaptation/epsilon-large-height-sourceproof-20261114/all-module-axioms.json" (Json.pretty (Json.arr out))
