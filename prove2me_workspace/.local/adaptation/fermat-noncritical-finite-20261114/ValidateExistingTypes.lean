import Lean
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalRamificationFinite

set_option autoImplicit false
open scoped IntermediateField

theorem PlatformAudit_noncriticalRamificationFinite : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M)
  (ψ : ↥M.K),
  Transcendental ℚ ψ →
    {P : AbcAdaptation.Tripod.Fermat.Proper.Place ↥M.K |
        1 < AbcAdaptation.Tripod.Fermat.Proper.ramIdx M hDVR ψ P}.Finite := by sorry

open Lean
run_meta do
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalRamificationFinite
  let p ← getConstInfo `PlatformAudit_noncriticalRamificationFinite
  unless ← Lean.Meta.isDefEq a.type p.type do throwError "Original platform target type differs: noncriticalRamificationFinite"
  IO.FS.writeFile ".local/adaptation/fermat-noncritical-finite-20261114/existing-types-equal.json" "true"
