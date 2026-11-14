import Definitions.Def_FermatCanonicalBelyiComposition
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiActualFieldDifferentAccounting
import Solutions.Source_FermatBelyiDifferentConductorAdapters
import Solutions.Source_FermatBelyiConductorExtensionAdapters
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiActualFieldDifferentTower
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_tripodGeneratorConductorIdentity

open AbcAdaptation.Tripod.Fermat.Proper

#print axioms canonicalEstimate_of_belyi_children
#print axioms belyiActualFieldDifferentAccounting
#print axioms belyiActualFieldConductorExtension_of_local_and_accounting
#print axioms belyiDifferentConductorComparison_of_exact_children
#print axioms belyiActualFieldDifferentTower
#print axioms tripodGeneratorConductorIdentity

example (hLocal : BelyiActualFieldLocalConductorComparison)
    (hInput : ∀ N : ℕ, 3 < N → NoncriticalInput N)
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
    (hStrictHeight : DivisorDegreeHeightComparison)
    (hConductor : CuspConductorHeightComparison) :
    AbcAdaptation.Tripod.Fermat.CanonicalEstimate :=
  canonicalEstimate_of_belyi_children hInput hCompact hRegular hEmbedding hChoices
    hDegree hCanonical hHeight hStrictHeight
    (belyiDifferentConductorComparison_of_exact_children
      (belyiActualFieldConductorExtension_of_local_and_accounting hLocal belyiActualFieldDifferentAccounting)
      belyiActualFieldDifferentTower tripodGeneratorConductorIdentity) hConductor
