import Lean
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_infinityDivisorExists
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_canonicalDivisorDegree

set_option autoImplicit false
open scoped IntermediateField

theorem PlatformAudit_infinityDivisorExists : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M),
  AbcAdaptation.Tripod.Fermat.Proper.ResiduesFinite M →
    Nonempty (AbcAdaptation.Tripod.Fermat.Proper.InfinityDivisorData M hDVR) := by sorry

theorem PlatformAudit_canonicalDivisorDegree : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M),
  3 < N →
    AbcAdaptation.Tripod.Fermat.Proper.ResiduesFinite M →
      ∀ (K : AbcAdaptation.Tripod.Fermat.Proper.CanonicalDivisorData M hDVR)
        (H : AbcAdaptation.Tripod.Fermat.Proper.InfinityDivisorData M hDVR)
        (J : AbcAdaptation.Tripod.Fermat.Proper.PlaneAdjunctionData M hDVR K H),
        AbcAdaptation.Tripod.Fermat.Proper.divisorDegree M K.D =
          AbcAdaptation.Tripod.Fermat.Proper.planeCanonicalDegree N := by sorry

open Lean
run_meta do
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.infinityDivisorExists
  let p ← getConstInfo `PlatformAudit_infinityDivisorExists
  unless ← Lean.Meta.isDefEq a.type p.type do throwError "Original platform target type differs: infinityDivisorExists"
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.canonicalDivisorDegree
  let p ← getConstInfo `PlatformAudit_canonicalDivisorDegree
  unless ← Lean.Meta.isDefEq a.type p.type do throwError "Original platform target type differs: canonicalDivisorDegree"
  IO.FS.writeFile ".local/adaptation/fermat-canonical-decomposition-20261114/existing-types-equal.json" "true"
