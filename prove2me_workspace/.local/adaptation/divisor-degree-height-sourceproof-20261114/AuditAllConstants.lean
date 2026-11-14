import Lean
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_divisorDegreeHeightComparison
open Lean
run_meta do
  let env ← getEnv
  let modules : Array Name := #[`Solutions.Source_FermatPolarAbsoluteExtension,`Solutions.Source_FermatPolarAbsoluteBasic,`Solutions.Source_FermatPolarPointAdapters,`Solutions.Source_FermatPolarTupleHeight,`Solutions.Source_FermatPolarMinOrd,`Solutions.Source_FermatPolarRootBound,`Solutions.Source_FermatPolarIntegrality,`Solutions.Source_FermatPolarPresentationHeights,`Solutions.Source_FermatDivisorTupleEquivalence,`Solutions.Source_FermatPositiveDegreePolar,`Solutions.Source_FermatDivisorHeightMachine,`Solutions.Source_FermatDivisorDegreeHeightComparison,`Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_divisorDegreeHeightComparison]
  let mut rows : Array Json := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some m := env.header.moduleNames[idx.toNat]? | continue
    unless modules.contains m do continue
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    rows := rows.push (Json.mkObj [("name",toJson name.toString),("module",toJson m.toString),("axioms",toJson (axs.map toString))])
  IO.FS.writeFile ".local/adaptation/divisor-degree-height-sourceproof-20261114/all-module-axioms.json" (Json.pretty (Json.arr rows))
