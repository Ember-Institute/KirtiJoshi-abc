import Lean
import Solutions.Source_TripodCurveInputsFromSource


open Lean Elab Command Meta in
run_meta do
  let env ← getEnv
  let owners := #[
    `Solutions.Source_TripodTorsionBasis,
    `Solutions.Source_TripodLogCond,
    `Solutions.Source_TripodCurveInputsFromSource]
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
