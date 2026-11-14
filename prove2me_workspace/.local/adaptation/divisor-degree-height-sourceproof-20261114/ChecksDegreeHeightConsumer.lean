import Definitions.Def_FermatCanonicalBelyiComposition
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_divisorDegreeHeightComparison

open AbcAdaptation.Tripod.Fermat.Proper

#print axioms canonicalEstimate_of_belyi_children
#print axioms divisorDegreeHeightComparison

example (hInput : ∀ N : ℕ, 3 < N → NoncriticalInput N)
    (hCompact : ∀ {N : ℕ} (M : Model N), PlacesDiscrete M →
      ResiduesFinite M → LocalCompactness M)
    (hRegular : ∀ {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M),
      AvoidanceRegularity M hDVR)
    (hEmbedding : ∀ {N : ℕ} (M : Model N), ResiduesFinite M → EmbeddingBoundsToSet M)
    (hChoices : ∀ {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M),
      3 < N → ResiduesFinite M → ∀ (φ : M.K), IsBelyi M hDVR φ →
      ∀ hfin : (cusps M hDVR φ).Finite,
        Nonempty (ArithmeticDivisorChoices M hDVR φ hfin))
    (hDegree : CanonicalDegreeIdentity)
    (hCanonical : CanonicalHeightIdentification)
    (hHeight : BelyiHeightRelation)
    (hDifferent : BelyiDifferentConductorComparison)
    (hConductor : CuspConductorHeightComparison) :
    AbcAdaptation.Tripod.Fermat.CanonicalEstimate :=
  canonicalEstimate_of_belyi_children hInput hCompact hRegular hEmbedding hChoices
    hDegree hCanonical hHeight divisorDegreeHeightComparison hDifferent hConductor
