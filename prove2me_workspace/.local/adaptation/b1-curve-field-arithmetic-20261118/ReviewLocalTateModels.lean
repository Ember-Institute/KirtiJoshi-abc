import Lean
import Solutions.Source_ReferenceIutTateStructureOfTorsion

open Lean Elab Command Meta in
run_meta do
  let env ← getEnv
  let owners := #[
    `Solutions.Source_ReferenceIutUltrametricSqrt,
    `Solutions.Source_ReferenceIutVariableChangePoint,
    `Solutions.Source_ReferenceIutTateLocalModels,
    `Solutions.Source_ReferenceIutTateIsomorphism,
    `Solutions.Source_ReferenceIutTateUniformization,
    `Solutions.Source_ReferenceIutTateStructureOfTorsion]
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
