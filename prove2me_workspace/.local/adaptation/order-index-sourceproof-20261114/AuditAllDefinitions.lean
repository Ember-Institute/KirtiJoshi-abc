import Lean
import Definitions.Def_FermatNoncriticalOrderSource
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalPolynomialOrderAtRegularPoint
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalPolynomialOrderAtPole
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalInverseRamification
open Lean
run_meta do
  let mods : Array Name := #[`Definitions.Def_FermatNoncriticalOrderSource, `Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalPolynomialOrderAtRegularPoint, `Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalPolynomialOrderAtPole, `Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalInverseRamification]
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
  IO.FS.writeFile ".local/adaptation/order-index-sourceproof-20261114/all-definition-axioms.json" (Json.pretty (Json.arr out))
