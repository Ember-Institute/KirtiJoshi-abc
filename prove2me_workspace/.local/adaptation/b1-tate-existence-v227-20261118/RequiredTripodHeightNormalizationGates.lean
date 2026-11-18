import ArithmeticTeichmullerSpaces.Prologue.Audit.Checks
import ArithmeticTeichmullerSpaces.Prologue.Audit.ImportAudit
import ArithmeticTeichmullerSpaces.Act1Scene1
import ArithmeticTeichmullerSpaces.Prologue.Audit.AxiomAudit
import Lean
import Solutions.Source_TripodProviderAuxiliaryHeight

#print axioms AbcAdaptation.Tripod.tripodalFieldOf_eq
#print axioms AbcAdaptation.Tripod.tpdEquiv_jT
#print axioms AbcAdaptation.Tripod.h_eq_finHeight_div
#print axioms AbcAdaptation.Tripod.providerHeight_eq_auxiliaryHeight

open Lean Elab Command Meta in
run_meta do
  let env ← getEnv
  let owners := #[`Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FieldInvariant,
    `Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FieldLegendreFacts,
    `Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FieldIdentification,
    `Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FieldTransport,
    `Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_JTransport,
    `Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_HeightNormalization,
    `Solutions.Source_TripodProviderAuxiliaryHeight]
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
