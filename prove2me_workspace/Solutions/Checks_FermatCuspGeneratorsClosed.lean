import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_cuspGeneratorsExists

open AbcAdaptation.Tripod.Fermat.Proper

#check cuspGeneratorsExists
#print axioms riemannRochFiniteDimensional
#print axioms riemannRochDimensionUpperBound
#print axioms riemannRochEventuallyLinear
#print axioms largeEffectivePolarRealization_of_riemannChildren
#print axioms cuspGeneratorsExists

example {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    (hRF : ResiduesFinite M) (φ : M.K) (hφ : IsBelyi M hDVR φ)
    (hfin : (cusps M hDVR φ).Finite) :
    Nonempty (CuspGenerators M hDVR φ hfin) :=
  cuspGeneratorsExists M hDVR hRF φ hφ hfin
