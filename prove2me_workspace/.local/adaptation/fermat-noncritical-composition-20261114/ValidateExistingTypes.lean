import Lean
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalCompositionRamification

set_option autoImplicit false
open scoped IntermediateField

theorem PlatformAudit_noncriticalCompositionRamification : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M)
  (ψ : ↥M.K),
  Transcendental ℚ ψ →
    (∀ (P : AbcAdaptation.Tripod.Fermat.Proper.Place ↥M.K), 0 < AbcAdaptation.Tripod.Fermat.Proper.ramIdx M hDVR ψ P) ∧
      ∀ (hs : List AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.ElemMap)
        (x : AbcAdaptation.Tripod.Fermat.Proper.QbarPoint ↥M.K),
        Transcendental ℚ (AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.compK hs ψ) ∧
          AbcAdaptation.Tripod.Fermat.Proper.noncriticalValue M x
                (AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.compK hs ψ) =
              AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.evalComp hs
                (AbcAdaptation.Tripod.Fermat.Proper.noncriticalValue M x ψ) ∧
            AbcAdaptation.Tripod.Fermat.Proper.ramIdx M hDVR
                (AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.compK hs ψ) x.P =
              AbcAdaptation.Tripod.Fermat.Proper.ramIdx M hDVR ψ x.P *
                ↑(AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.ramIdxComp hs
                    (AbcAdaptation.Tripod.Fermat.Proper.noncriticalValue M x ψ)) := by sorry

open Lean
run_meta do
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalCompositionRamification
  let p ← getConstInfo `PlatformAudit_noncriticalCompositionRamification
  unless ← Lean.Meta.isDefEq a.type p.type do throwError "Original platform target type differs: noncriticalCompositionRamification"
  IO.FS.writeFile ".local/adaptation/fermat-noncritical-composition-20261114/existing-types-equal.json" "true"
