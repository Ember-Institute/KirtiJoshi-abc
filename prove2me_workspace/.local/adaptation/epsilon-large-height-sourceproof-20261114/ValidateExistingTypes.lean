import Lean
import Theorems.Thm_AbcAdaptation_Tripod_epsilonELargeHeight

theorem ExistingPlatformType : AbcAdaptation.Tripod.EpsilonELargeHeight := by sorry
open Lean
run_meta do
  let a ← getConstInfo `AbcAdaptation.Tripod.epsilonELargeHeight
  let c ← getConstInfo `ExistingPlatformType
  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Existing platform type differs"
  IO.FS.writeFile ".local/adaptation/epsilon-large-height-sourceproof-20261114/existing-types-equal.json" "true"
