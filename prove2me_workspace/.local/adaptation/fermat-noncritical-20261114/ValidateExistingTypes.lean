import Lean
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_cuspsFinite
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalSelection

set_option autoImplicit false
open scoped IntermediateField

theorem PlatformAudit_cuspsFinite : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M),
  AbcAdaptation.Tripod.Fermat.Proper.ResiduesFinite M →
    ∀ (φ : ↥M.K),
      AbcAdaptation.Tripod.Fermat.Proper.IsBelyi M hDVR φ → (AbcAdaptation.Tripod.Fermat.Proper.cusps M hDVR φ).Finite := by sorry

theorem PlatformAudit_noncriticalSelection : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M),
  AbcAdaptation.Tripod.Fermat.Proper.ResiduesFinite M → AbcAdaptation.Tripod.Fermat.Proper.NoncriticalSelection M hDVR := by sorry

open Lean
run_meta do
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.cuspsFinite
  let p ← getConstInfo `PlatformAudit_cuspsFinite
  unless ← Lean.Meta.isDefEq a.type p.type do throwError "Original platform target type differs: cuspsFinite"
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalSelection
  let p ← getConstInfo `PlatformAudit_noncriticalSelection
  unless ← Lean.Meta.isDefEq a.type p.type do throwError "Original platform target type differs: noncriticalSelection"
  IO.FS.writeFile ".local/adaptation/fermat-noncritical-20261114/existing-types-equal.json" "true"
