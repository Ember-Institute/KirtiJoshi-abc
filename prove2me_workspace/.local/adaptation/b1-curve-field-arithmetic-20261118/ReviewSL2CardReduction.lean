import Lean
import Solutions.Sketch_EllipticCurveData_sl_le_range_of
import Theorems.Thm_AbcAdaptation_Reference_Iut_EllipticCurveData_sl_le_range_of

open Lean Elab Command Meta in
run_meta do
  let parent := `AbcAdaptation.Reference.Iut.EllipticCurveData.sl_le_range_of
  let child := `AbcAdaptation.Reference.Iut.EllipticCurveData.prime_dvd_card_range
  let parentInfo ← getConstInfo parent
  let sketchInfo ← getConstInfo `solution
  let levels := parentInfo.levelParams.map Level.param
  unless parentInfo.levelParams.length == sketchInfo.levelParams.length do
    throwError "Parent and reduction have different universe arities"
  unless ← isDefEq parentInfo.type
      (sketchInfo.type.instantiateLevelParams sketchInfo.levelParams levels) do
    throwError "Reduction type differs from the parent type"
  let some body := sketchInfo.value? (allowOpaque := true) | throwError "Reduction proof is missing"
  let refs := body.getUsedConstantsAsSet
  unless refs.contains child && !refs.contains parent && !refs.contains `sorryAx do
    throwError "Reduction does not use the expected open theorem directly"
  let axioms ← collectAxioms `solution
  unless axioms.contains `sorryAx &&
      axioms.all (fun axiomName => #[`sorryAx, `propext, `Classical.choice, `Quot.sound].contains axiomName) do
    throwError "Unexpected reduction axioms {axioms}"
  logInfo m!"Reduction has the exact parent type and directly uses {child}. Axioms: {axioms}"
