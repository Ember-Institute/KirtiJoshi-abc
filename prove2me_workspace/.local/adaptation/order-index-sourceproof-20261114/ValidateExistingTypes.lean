import Lean
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalPolynomialOrderAtRegularPoint
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalPolynomialOrderAtPole
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalInverseRamification
set_option autoImplicit false
open AbcAdaptation
open AbcAdaptation.Tripod.Fermat.Proper

section
-- imported above: Definitions.Def_FermatNoncriticalElementarySource

set_option autoImplicit false
open Polynomial
open scoped IntermediateField
open AbcAdaptation
open AbcAdaptation.Tripod.Fermat.Proper
/-- OPEN: exact actual-function-field mathematical boundary from Belyi/CurveField/NoncriticalBasic.lean ord_aeval_eq. -/
theorem PlatformTarget_noncriticalPolynomialOrderAtRegularPoint {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ)
    (x : QbarPoint M.K) (h : ψ ∈ x.P.1) {g : ℚ[X]} (hg : g ≠ 0) :
    letI : IsCurveField M.K := M.isCurveField
    x.P.ord (aeval ψ g) = ramIdx M hDVR ψ x.P *
      ((g.map (algebraMap ℚ Tripod.Qbar)).rootMultiplicity (x.eval ψ h) : ℤ) := by
  letI : IsCurveField M.K := M.isCurveField
  sorry
end

section
-- imported above: Definitions.Def_FermatNoncriticalElementarySource

set_option autoImplicit false
open Polynomial
open scoped IntermediateField
open AbcAdaptation
open AbcAdaptation.Tripod.Fermat.Proper
/-- OPEN: exact actual-function-field mathematical boundary from Belyi/CurveField/NoncriticalElem.lean ord_aeval_of_notMem. -/
theorem PlatformTarget_noncriticalPolynomialOrderAtPole {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ)
    (P : Place M.K) (h : ψ ∉ P.1) {p : ℚ[X]} (hp : p ≠ 0) :
    letI : IsCurveField M.K := M.isCurveField
    P.ord (aeval ψ p) = p.natDegree * P.ord ψ := by
  letI : IsCurveField M.K := M.isCurveField
  sorry
end

section
-- imported above: Definitions.Def_FermatNoncriticalElementarySource

set_option autoImplicit false
open Polynomial
open scoped IntermediateField
open AbcAdaptation
open AbcAdaptation.Tripod.Fermat.Proper
/-- OPEN: exact actual-function-field mathematical boundary from Belyi/CurveField/NoncriticalElem.lean inv_spec second conjunct. -/
theorem PlatformTarget_noncriticalInverseRamification {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ)
    (x : QbarPoint M.K) :
    ramIdx M hDVR ψ⁻¹ x.P = ramIdx M hDVR ψ x.P := by
  letI : IsCurveField M.K := M.isCurveField
  sorry
end

open Lean
run_meta do
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalPolynomialOrderAtRegularPoint
  let b ← getConstInfo `PlatformTarget_noncriticalPolynomialOrderAtRegularPoint
  unless ← Lean.Meta.isDefEq a.type b.type do throwError "Platform target differs: noncriticalPolynomialOrderAtRegularPoint"
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalPolynomialOrderAtPole
  let b ← getConstInfo `PlatformTarget_noncriticalPolynomialOrderAtPole
  unless ← Lean.Meta.isDefEq a.type b.type do throwError "Platform target differs: noncriticalPolynomialOrderAtPole"
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalInverseRamification
  let b ← getConstInfo `PlatformTarget_noncriticalInverseRamification
  unless ← Lean.Meta.isDefEq a.type b.type do throwError "Platform target differs: noncriticalInverseRamification"
  IO.FS.writeFile ".local/adaptation/order-index-sourceproof-20261114/existing-types-equal.json" "true"
