import Lean
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_placesDiscrete
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_residuesFinite
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_polarPresentationExists

set_option autoImplicit false
open scoped IntermediateField

theorem PlatformAudit_placesDiscrete : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N), AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M := by sorry

theorem PlatformAudit_residuesFinite : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N), AbcAdaptation.Tripod.Fermat.Proper.ResiduesFinite M := by sorry

theorem PlatformAudit_polarPresentationExists : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M),
  AbcAdaptation.Tripod.Fermat.Proper.ResiduesFinite M →
    ∀ (D : AbcAdaptation.Tripod.Fermat.Proper.Divisor M),
      Nonempty (AbcAdaptation.Tripod.Fermat.Proper.PolarPresentation M hDVR D) := by sorry

open Lean
run_meta do
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.placesDiscrete
  let p ← getConstInfo `PlatformAudit_placesDiscrete
  unless ← Lean.Meta.isDefEq a.type p.type do throwError "Original platform target type differs: placesDiscrete"
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.residuesFinite
  let p ← getConstInfo `PlatformAudit_residuesFinite
  unless ← Lean.Meta.isDefEq a.type p.type do throwError "Original platform target type differs: residuesFinite"
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.polarPresentationExists
  let p ← getConstInfo `PlatformAudit_polarPresentationExists
  unless ← Lean.Meta.isDefEq a.type p.type do throwError "Original platform target type differs: polarPresentationExists"
  IO.FS.writeFile ".local/adaptation/fermat-riemann-20261113/existing-types-equal.json" "true"
