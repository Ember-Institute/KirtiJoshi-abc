/- Exact parent/consumer acceptance checks for the source height comparison. -/
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_polarPresentationHeightSum_of_principalRelation
import Solutions.Source_FermatBelyiHeightComparison

set_option autoImplicit false
namespace AbcAdaptation.Tripod.Fermat.Proper

#check polarPresentationHeightSum_of_principalRelation
#print axioms polarPresentationHeightSum_of_principalRelation
#print axioms polarPresentationHeightSum_of_tupleMonotonicity
#print axioms PolarTuple.tupleHeight_pairOne_eq_functionHeight
#print axioms PolarTuple.tupleHeight_le_of_minOrd_le
#print axioms PolarAbsolute.logHeight_comp_ringHom_div_finrank

/-- Exact current consumer, with its actual canonical/cusp presentations.
The geometry input is intentionally retained; no claim about its closure. -/
example
    (hGeometry : ∀ {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
      (hRF : ResiduesFinite M) (φ : M.K) (hφ : IsBelyi M hDVR φ)
      (hfin : (cusps M hDVR φ).Finite) (K : CanonicalDivisorData M hDVR),
      ∃ r : M.K, r ≠ 0 ∧ ∀ P : Place M.K,
        K.D P + cuspDivisor M hDVR φ hfin P =
          poleMultiplicity M hDVR φ P + ord M hDVR P r) :
    BelyiHeightRelation := by
  exact belyiHeightRelation_of_children hGeometry
    polarPresentationHeightSum_of_principalRelation

end AbcAdaptation.Tripod.Fermat.Proper
