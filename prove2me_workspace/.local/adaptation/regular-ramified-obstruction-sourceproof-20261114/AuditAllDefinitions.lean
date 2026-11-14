import Lean
import Definitions.Def_FermatCurveFieldUniformizer
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_exists_irreducible_valuation_lt_one
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_valuation_aeval_derivative_eq_one
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_exists_pow_succ_mul_derivAlong_not_mem
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_exists_eq_div
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_exists_pow_mul_derivAlong_mem_integralClosure
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_exists_pow_mul_derivAlong_mem
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_derivAlong_mem
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_derivAlong_unit_mul_pow
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_derivAlong_eq_unit_mul_pow_of_aeval
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalRegularRamifiedDerivNotMem
open Lean
run_meta do
  let mods : Array Name := #[`Definitions.Def_FermatCurveFieldUniformizer, `Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_exists_irreducible_valuation_lt_one, `Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_valuation_aeval_derivative_eq_one, `Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_exists_pow_succ_mul_derivAlong_not_mem, `Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_exists_eq_div, `Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_exists_pow_mul_derivAlong_mem_integralClosure, `Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_exists_pow_mul_derivAlong_mem, `Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_derivAlong_mem, `Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_derivAlong_unit_mul_pow, `Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_derivAlong_eq_unit_mul_pow_of_aeval, `Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalRegularRamifiedDerivNotMem]
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
  IO.FS.writeFile ".local/adaptation/regular-ramified-obstruction-sourceproof-20261114/all-module-axioms.json" (Json.pretty (Json.arr out))
