import ArithmeticTeichmullerSpaces.Prologue.Audit.Checks
import ArithmeticTeichmullerSpaces.Prologue.Audit.ImportAudit
import ArithmeticTeichmullerSpaces.Act1Scene1
import ArithmeticTeichmullerSpaces.Prologue.Audit.AxiomAudit
import Lean
import Solutions.Source_TripodPlaceUnder
import Solutions.Source_TripodRelativeValuation

#print axioms AbcAdaptation.Tripod.placeUnder_eq_of_liesOver_place
#print axioms AbcAdaptation.Tripod.valuation_algebraMap_eq_pow

open Lean Elab Command Meta in
run_meta do
  let env ← getEnv
  let owners := #[`Solutions.Source_TripodPlaceUnder, `Solutions.Source_TripodRelativeValuation]
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
