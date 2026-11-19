import Lean
import Solutions.Sketch_Tripod_cyclicBoundOdd
import Theorems.Thm_AbcAdaptation_Tripod_cyclicBoundOdd

open Lean Elab Command Meta in
run_meta do
  let parent := `AbcAdaptation.Tripod.cyclicBoundOdd
  let children := #[
    `AbcAdaptation.Tripod.cyclicLocalGraphLine,
    `AbcAdaptation.Tripod.legendre_torsion_x_le,
    `AbcAdaptation.Tripod.Cyclic.main_bound]
  let parentInfo ← getConstInfo parent
  let sketchInfo ← getConstInfo `solution
  let levels := parentInfo.levelParams.map Level.param
  unless parentInfo.levelParams.length == sketchInfo.levelParams.length do
    throwError "Parent and reduction have different universe arities"
  unless ← isDefEq parentInfo.type
      (sketchInfo.type.instantiateLevelParams sketchInfo.levelParams levels) do
    throwError "Reduction type differs from the parent type"
  let some body := sketchInfo.value? (allowOpaque := true) |
    throwError "Reduction proof is missing"
  let refs := body.getUsedConstantsAsSet
  unless children.all (fun child => refs.contains child) &&
      !refs.contains parent && !refs.contains `sorryAx do
    throwError "Reduction has unexpected direct dependencies"
  let axioms ← collectAxioms `solution
  unless axioms.contains `sorryAx &&
      axioms.all (fun name => #[`sorryAx, `propext, `Classical.choice, `Quot.sound].contains name) do
    throwError "Unexpected reduction axioms {axioms}"
  logInfo m!"Reduction uses all three children and has the same type as its parent. Axioms {axioms}"
