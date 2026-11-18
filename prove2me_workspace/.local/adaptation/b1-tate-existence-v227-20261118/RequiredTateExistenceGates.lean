import ArithmeticTeichmullerSpaces.Prologue.Audit.Checks
import ArithmeticTeichmullerSpaces.Prologue.Audit.ImportAudit
import ArithmeticTeichmullerSpaces.Act1Scene1
import ArithmeticTeichmullerSpaces.Prologue.Audit.AxiomAudit
import Lean
import Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_QParameter_JExistence

#print axioms AbcAdaptation.Reference.TateCurvesTheta.TateParameter.exists_tateParameter_tateJ_eq

open Lean Elab Command Meta in
run_meta do
  let env ← getEnv
  let owners : Array Name := #[
    `Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_Discriminant,
    `Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_QParameter_JExistence]
  let names := env.constants.fold (fun result name _ =>
    match env.getModuleIdxFor? name with
    | none => result
    | some index => if (env.header.moduleNames[index.toNat]?).any owners.contains then result.push name else result)
    (#[] : Array Name)
  unless names.size > 0 do throwError "No declarations owned by the migrated modules"
  for name in names.qsort Name.lt do
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Unexpected axiom {axiomName} in {name}"
    logInfo m!"{name}: standard axioms {axioms}"
  logInfo m!"Audited {names.size} owned declarations"
