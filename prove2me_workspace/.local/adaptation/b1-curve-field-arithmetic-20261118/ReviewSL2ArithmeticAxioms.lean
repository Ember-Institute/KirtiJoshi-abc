import Lean
import Solutions.Source_SL2ImageRangeCardinality
import Solutions.Source_ReferenceIutTateTorsion
import Solutions.Source_SL2ImageLocalValuation


open Lean Elab Command Meta in
run_meta do
  let env ← getEnv
  let owners := #[
    `Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_ModEllRepTorsionField,
    `Solutions.Source_ModEllRepGalois,
    `Solutions.Source_SL2ImageRangeCardinality,
    `Solutions.Source_ReferenceIutTateTorsion,
    `Solutions.Source_SL2ImageLocalValuation]
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
