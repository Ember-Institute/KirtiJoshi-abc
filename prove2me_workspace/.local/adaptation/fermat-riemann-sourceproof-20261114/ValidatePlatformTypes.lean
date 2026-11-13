import Lean
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_functionZeroPoleDegrees
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_riemannPolarApproximation
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_riemannBasisPowerLowerBound
open scoped IntermediateField
set_option autoImplicit false

theorem PlatformTarget_functionZeroPoleDegrees : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M)
  (f : ↥M.K),
  Transcendental ℚ f →
    AbcAdaptation.Tripod.Fermat.Proper.divisorDegree M
          (AbcAdaptation.Tripod.Fermat.Proper.functionZeroDivisor M hDVR f) =
        ↑(Module.finrank ↥ℚ⟮f⟯ ↥M.K) ∧
      AbcAdaptation.Tripod.Fermat.Proper.divisorDegree M
          (AbcAdaptation.Tripod.Fermat.Proper.functionPoleDivisor M hDVR f) =
        ↑(Module.finrank ↥ℚ⟮f⟯ ↥M.K) := by sorry

theorem PlatformTarget_riemannPolarApproximation : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M)
  (A : AbcAdaptation.Tripod.Fermat.Proper.Divisor M),
  ∃ (z : ↥M.K),
    z ≠ 0 ∧
      ∃ (l : ℕ),
        A + AbcAdaptation.Tripod.Fermat.Proper.functionDivisor M hDVR z ≤
          l • AbcAdaptation.Tripod.Fermat.Proper.functionPoleDivisor M hDVR M.u := by sorry

theorem PlatformTarget_riemannBasisPowerLowerBound : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M),
  (∀ (A : AbcAdaptation.Tripod.Fermat.Proper.Divisor M),
      FiniteDimensional ℚ ↥(AbcAdaptation.Tripod.Fermat.Proper.riemannRochSpace M hDVR A)) →
    ∀ (l : ℕ),
      (l + 1) * N ≤
        AbcAdaptation.Tripod.Fermat.Proper.riemannEll M hDVR
          (l • AbcAdaptation.Tripod.Fermat.Proper.functionPoleDivisor M hDVR M.u +
            AbcAdaptation.Tripod.Fermat.Proper.basisPoleCorrection M hDVR) := by sorry

open Lean
run_meta do
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.functionZeroPoleDegrees
  let b ← getConstInfo `PlatformTarget_functionZeroPoleDegrees
  unless ← Lean.Meta.isDefEq a.type b.type do throwError "Target type differs: functionZeroPoleDegrees"
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.riemannPolarApproximation
  let b ← getConstInfo `PlatformTarget_riemannPolarApproximation
  unless ← Lean.Meta.isDefEq a.type b.type do throwError "Target type differs: riemannPolarApproximation"
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.riemannBasisPowerLowerBound
  let b ← getConstInfo `PlatformTarget_riemannBasisPowerLowerBound
  unless ← Lean.Meta.isDefEq a.type b.type do throwError "Target type differs: riemannBasisPowerLowerBound"
  IO.FS.writeFile ".local/adaptation/fermat-riemann-sourceproof-20261114/platform-types-equal.json" "true"
