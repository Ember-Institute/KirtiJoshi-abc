import Lean
import Solutions.Sketch_Tripod_legendre_torsion_x_le
import Theorems.Thm_AbcAdaptation_Tripod_legendre_torsion_x_le

open Lean Elab Command Meta in
run_meta do
  let parent := `AbcAdaptation.Tripod.legendre_torsion_x_le
  let child := `AbcAdaptation.Reference.Heights.exists_torsion_x_bound
  let proof := `AbcAdaptation.Tripod.legendre_torsion_x_le_of_complex
  let parentInfo ← getConstInfo parent
  let sketchInfo ← getConstInfo `solution
  unless ← isDefEq parentInfo.type sketchInfo.type do
    throwError "The Legendre reduction type differs from its parent type"
  let some body := sketchInfo.value? (allowOpaque := true) |
    throwError "The Legendre reduction proof is missing"
  let refs := body.getUsedConstantsAsSet
  unless refs.contains child && refs.contains proof &&
      !refs.contains parent && !refs.contains `sorryAx do
    throwError "The Legendre reduction has unexpected direct dependencies"
  let axioms ← collectAxioms `solution
  unless axioms.contains `sorryAx &&
      axioms.all (fun name => #[`sorryAx, `propext, `Classical.choice, `Quot.sound].contains name) do
    throwError "Unexpected Legendre reduction axioms {axioms}"
  logInfo m!"The Legendre reduction has the parent's type and uses the complex torsion node"
