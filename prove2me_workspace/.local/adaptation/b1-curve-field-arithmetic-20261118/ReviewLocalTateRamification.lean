import Lean
import Solutions.Source_SL2ImageLocalTate

open Lean Elab Command Meta in
run_meta do
  let env ← getEnv
  let owners := #[
    `Solutions.Source_ReferenceIutSplitSquare,
    `Solutions.Source_ReferenceIutTateUniformizationLaws,
    `Solutions.Source_SL2ImageLocalTate]
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
