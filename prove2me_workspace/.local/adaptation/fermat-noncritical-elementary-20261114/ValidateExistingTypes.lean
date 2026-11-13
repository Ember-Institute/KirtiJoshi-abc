import Lean
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalElementaryCompositionRamification

set_option autoImplicit false
open Polynomial
open scoped IntermediateField
open AbcAdaptation
open AbcAdaptation.Tripod.Fermat.Proper

/-- OPEN: the actual single-elementary-map composition step from the source.
The map is a rational Möbius transformation with nonzero determinant or a
positive-degree rational polynomial. Every actual residue embedding is kept. -/
theorem PlatformAudit_noncriticalElementaryCompositionRamification {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ)
    (x : QbarPoint M.K) (h : NoncriticalP1.ElemMap) :
    Transcendental ℚ (NoncriticalP1.applyK h ψ) ∧
    noncriticalValue M x (NoncriticalP1.applyK h ψ) = h.apply (noncriticalValue M x ψ) ∧
    ramIdx M hDVR (NoncriticalP1.applyK h ψ) x.P =
      ramIdx M hDVR ψ x.P * (h.ramIdx (noncriticalValue M x ψ) : ℤ) := by
  sorry

open Lean
run_meta do
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalElementaryCompositionRamification
  let p ← getConstInfo `PlatformAudit_noncriticalElementaryCompositionRamification
  unless ← Lean.Meta.isDefEq a.type p.type do throwError "Original platform target type differs: noncriticalElementaryCompositionRamification"
  IO.FS.writeFile ".local/adaptation/fermat-noncritical-elementary-20261114/existing-types-equal.json" "true"
