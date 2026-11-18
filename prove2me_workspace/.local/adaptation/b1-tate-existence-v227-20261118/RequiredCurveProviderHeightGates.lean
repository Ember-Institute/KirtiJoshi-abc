import ArithmeticTeichmullerSpaces.Prologue.Audit.Checks
import ArithmeticTeichmullerSpaces.Prologue.Audit.ImportAudit
import ArithmeticTeichmullerSpaces.Act1Scene1
import ArithmeticTeichmullerSpaces.Prologue.Audit.AxiomAudit
import Lean
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviderHeight

#print axioms AbcAdaptation.Tripod.CurveProviders.h

open Lean Elab Command Meta in
run_meta do
  for name in #[`AbcAdaptation.Tripod.CurveProviders.tate,
    `AbcAdaptation.Tripod.CurveProviders.localData, `AbcAdaptation.Tripod.CurveProviders.h] do
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Unexpected axiom {axiomName} in {name}"
    logInfo m!"{name}: standard axioms {axioms}"
