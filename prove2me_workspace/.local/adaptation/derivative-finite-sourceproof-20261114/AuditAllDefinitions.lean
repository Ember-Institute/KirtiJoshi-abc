import Lean
import Definitions.Def_FermatCurveDerivationAdjoin
import Definitions.Def_FermatCurveDerivationLocalization
open Lean
run_meta do
  let mods : Array Name := #[`Definitions.Def_FermatCurveDerivationAdjoin, `Definitions.Def_FermatCurveDerivationLocalization]
  let env ← getEnv
  let mut out : Array Json := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some m := env.header.moduleNames[idx.toNat]? | continue
    unless mods.contains m do continue
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do throwError "Unapproved axiom {ax} in {name}"
    out := out.push (Json.mkObj [("name", toJson name.toString), ("axioms", toJson (axs.map toString))])
  IO.FS.writeFile ".local/adaptation/derivative-finite-sourceproof-20261114/all-definition-axioms.json" (Json.pretty (Json.arr out))
