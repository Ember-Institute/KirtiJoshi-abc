import ArithmeticTeichmullerSpaces.Prologue.Audit.Checks
import ArithmeticTeichmullerSpaces.Prologue.Audit.ImportAudit
import ArithmeticTeichmullerSpaces.Act1Scene1
import ArithmeticTeichmullerSpaces.Prologue.Audit.AxiomAudit
import Lean
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FiniteHeightSum

#print axioms AbcAdaptation.Tripod.finrank_mul_h_eq_finHeight

open Lean Elab Command Meta in
run_meta do
  let env ← getEnv
  let owner := `Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FiniteHeightSum
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
