import ArithmeticTeichmullerSpaces.Prologue.Audit.Checks
import ArithmeticTeichmullerSpaces.Prologue.Audit.ImportAudit
import ArithmeticTeichmullerSpaces.Act1Scene1
import ArithmeticTeichmullerSpaces.Prologue.Audit.AxiomAudit
import Lean
import Solutions.Source_TripodCurveInputsHeightFields

#print axioms AbcAdaptation.Tripod.northcottHyp
#print axioms AbcAdaptation.Tripod.northcott_of_equiv
#print axioms AbcAdaptation.Tripod.curveInputs_htCan_equiv
#print axioms AbcAdaptation.Tripod.curveInputs_height_eq
#print axioms AbcAdaptation.Tripod.curveInputs_northcott

open Lean Elab Command Meta in
run_meta do
  let env ← getEnv
  let owners := #[`Definitions.Def_AbcAdaptation_Reference_Genl_DiscrepancyEquivGe,
    `Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_NorthcottComparison,
    `Solutions.Source_TripodCurveInputsHeightFields]
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
