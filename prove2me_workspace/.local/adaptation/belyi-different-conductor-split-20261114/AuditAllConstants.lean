import Lean
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiDifferentConductorComparison
open Lean
run_meta do
  let env ← getEnv
  let closed : Array Name := #[`Definitions.Def_FermatBelyiDifferentConductorChildren,`Solutions.Source_FermatBelyiDifferentConductorAdapters,`Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiActualFieldDifferentTower,`Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_tripodGeneratorConductorIdentity]
  let opened : Array Name := #[`Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiActualFieldConductorExtension,`Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiDifferentConductorComparison]
  let mut rows : Array Json := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some m := env.header.moduleNames[idx.toNat]? | continue
    unless closed.contains m || opened.contains m do continue
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax || (opened.contains m && ax == `sorryAx) do
        throwError "Unexpected axiom {ax} in {name}"
    if opened.contains m then
      unless axs.contains `sorryAx do throwError "Expected explicit open source debt in {name}"
    rows := rows.push (Json.mkObj [("name",toJson name.toString),("module",toJson m.toString),("open_dependency_expected",toJson (opened.contains m)),("axioms",toJson (axs.map toString))])
  IO.FS.writeFile ".local/adaptation/belyi-different-conductor-split-20261114/all-module-axioms.json" (Json.pretty (Json.arr rows))
