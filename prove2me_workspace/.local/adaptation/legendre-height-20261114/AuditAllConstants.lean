import Lean
import Solutions.Sol_CanonicalLegendreHeightComparison
import Theorems.Thm_AbcAdaptation_Tripod_canonicalLegendreHeightComparison

open Lean
run_meta do
  let env ← getEnv
  let modules : Array Name := #[`Definitions.Def_TripodLegendreHeightComparisonInputs, `Definitions.Def_TripodLegendreHeightBasics, `Definitions.Def_TripodLegendreHeightComparisonComposition, `Theorems.Thm_AbcAdaptation_Tripod_legendreArchimedeanTripleBound, `Theorems.Thm_AbcAdaptation_Tripod_legendreZeroJRootOfUnity]
  let mut out : Array Json := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some m := env.header.moduleNames[idx.toNat]? | continue
    unless modules.contains m do continue
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do throwError "Unapproved axiom {ax} in {name}"
    out := out.push (Json.mkObj [("name", toJson name.toString), ("module", toJson m.toString), ("axioms", toJson (axs.map toString))])
  IO.FS.writeFile ".local/adaptation/legendre-height-20261114/all-module-axioms.json" (Json.pretty (Json.arr out))
