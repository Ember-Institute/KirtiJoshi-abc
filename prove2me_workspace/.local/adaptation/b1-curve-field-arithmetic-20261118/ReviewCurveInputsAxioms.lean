import Lean
import Solutions.Source_TripodCurveInputs
import Solutions.Source_ModEllRepStableLine

#print axioms AbcAdaptation.Tripod.curveInputs_deg_le
#print axioms AbcAdaptation.Tripod.curveInputs_logDiff_eq
#print axioms AbcAdaptation.Tripod.curveInputsOfSL2Image
#print axioms AbcAdaptation.Reference.Iut.CurveInputs.toCorollary22Inputs
#print axioms AbcAdaptation.Reference.Iut.EllipticCurveData.ModEllRepData.exists_mulVec_ne_smul_of_not_hasCyclicSubgroup

open Lean Elab Command Meta in
run_meta do
  let env ← getEnv
  let owners := #[
    `Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants,
    `Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs,
    `Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveDegreeBound,
    `Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_DifferentDegree,
    `Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveFacts,
    `Solutions.Source_TripodCurveInputsFieldArithmetic,
    `Solutions.Source_TripodCurveInputs,
    `Solutions.Source_ModEllRepStableLine]
  for owner in owners do
    let names := env.constants.fold (fun names name _ =>
      if (env.getModuleIdxFor? name).any (fun i => env.header.moduleNames[i.toNat]? == some owner)
      then names.push name else names) (#[] : Array Name)
    unless !names.isEmpty do throwError "No declarations owned by {owner}"
    for name in names.qsort Name.lt do
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Unexpected axiom {axiomName} in {name}"
      logInfo m!"{name}: standard axioms {axioms}"
    logInfo m!"Audited {names.size} owned declarations in {owner}"
