import Lean
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiHeightRelation
open Lean
run_meta do
  let env ← getEnv
  let closedModule := `Solutions.Source_FermatBelyiHeightComparison
  let openModules : Array Name := #[`Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_canonicalCuspPolarLinearEquivalence,`Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_polarPresentationHeightSum_of_principalRelation,`Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiHeightRelation]
  let mut rows : Array Json := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some m := env.header.moduleNames[idx.toNat]? | continue
    unless m == closedModule || openModules.contains m do continue
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax || (m != closedModule && ax == `sorryAx) do
        throwError "Unexpected axiom {ax} in {name}"
    if openModules.contains m then
      unless axs.contains `sorryAx do throwError "Expected explicit open dependency in {name}"
    rows := rows.push (Json.mkObj [("name",toJson name.toString),("module",toJson m.toString),("open_dependency_expected",toJson (m != closedModule)),("axioms",toJson (axs.map toString))])
  IO.FS.writeFile ".local/adaptation/belyi-height-split-20261114/all-module-axioms.json" (Json.pretty (Json.arr rows))
