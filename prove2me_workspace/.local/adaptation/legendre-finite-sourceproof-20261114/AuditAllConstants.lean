import Lean
import Solutions.Sol_LegendreFiniteSourceClosure
open Lean
run_meta do
  let env ← getEnv
  let mods : Array Name := #[`Solutions.Source_TripodFiniteHeightSupport,`Solutions.Source_TripodFinitePlaceArithmetic,`Solutions.Source_TripodFinitePrimeCounting,`Solutions.Source_TripodLegendreFinitePlaceBounds,`Solutions.Source_TripodLegendreValuationBounds,`Theorems.Thm_AbcAdaptation_Tripod_legendreFiniteUpperBound,`Theorems.Thm_AbcAdaptation_Tripod_legendreFiniteLowerBound]
  let mut out : Array Json := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some m := env.header.moduleNames[idx.toNat]? | continue
    unless mods.contains m do continue
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do throwError "Unexpected axiom {ax} in {name}"
    out := out.push (Json.mkObj [("name", toJson name.toString), ("module", toJson m.toString), ("axioms", toJson (axs.map toString))])
  IO.FS.writeFile ".local/adaptation/legendre-finite-sourceproof-20261114/all-module-axioms.json" (Json.pretty (Json.arr out))
