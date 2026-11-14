import Lean
import Definitions.Def_TripodNorthcottInputs
import Definitions.Def_TripodNorthcottComposition
import Theorems.Thm_AbcAdaptation_Tripod_Northcott_norm_embedding_le_mulHeight_one
import Theorems.Thm_AbcAdaptation_Tripod_Northcott_mulHeight_one_gen_le
import Theorems.Thm_AbcAdaptation_Tripod_Northcott_coeff_minpoly_int_mem_Icc
import Theorems.Thm_AbcAdaptation_Tripod_northcottFiniteRoots
import Theorems.Thm_AbcAdaptation_Tripod_northcottPolynomialWitness
import Theorems.Thm_AbcAdaptation_Tripod_boundedDegreeFiniteness
open Lean
run_meta do
  let mods : Array Name := #[`Definitions.Def_TripodNorthcottInputs, `Definitions.Def_TripodNorthcottComposition, `Theorems.Thm_AbcAdaptation_Tripod_Northcott_norm_embedding_le_mulHeight_one, `Theorems.Thm_AbcAdaptation_Tripod_Northcott_mulHeight_one_gen_le, `Theorems.Thm_AbcAdaptation_Tripod_Northcott_coeff_minpoly_int_mem_Icc, `Theorems.Thm_AbcAdaptation_Tripod_northcottFiniteRoots, `Theorems.Thm_AbcAdaptation_Tripod_northcottPolynomialWitness, `Theorems.Thm_AbcAdaptation_Tripod_boundedDegreeFiniteness]
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
  IO.FS.writeFile ".local/adaptation/northcott-sourceproof-20261114/all-module-axioms.json" (Json.pretty (Json.arr out))
