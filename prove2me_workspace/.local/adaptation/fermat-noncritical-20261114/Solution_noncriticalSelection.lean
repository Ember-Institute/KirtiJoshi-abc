import Definitions.Def_FermatNoncriticalComposition
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_riemannRochFiniteDimensional
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_riemannRochDimensionUpperBound
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_riemannRochEventuallyLinear
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalRamificationFinite
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalCompositionRamification
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalP1Zero

set_option autoImplicit false
open scoped IntermediateField
open AbcAdaptation.Tripod.Fermat.Proper

/-- Candidate replacement, retaining the complete original selection type.
The Riemann children produce simple zeros at a superset of T. The three
new children then produce the actual φ and prove its all-place Belyi and
avoidance properties through the actual branch-value set and chain rule. -/
theorem solution {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    (hRF : ResiduesFinite M) : NoncriticalSelection M hDVR := by
  have hRealize := largeEffectivePolarRealization_of_riemannChildren M hDVR
    (riemannRochFiniteDimensional M hDVR)
    (riemannRochDimensionUpperBound M hDVR)
    (riemannRochEventuallyLinear M hDVR)
  exact noncriticalSelection_of_simpleZeros_and_children M hDVR
    (simpleZeroFunction_of_polarRealization M hDVR hRealize)
    (noncriticalRamificationFinite M hDVR)
    (noncriticalCompositionRamification M hDVR) noncriticalP1Zero
