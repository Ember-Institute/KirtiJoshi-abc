/-
Independent source-proof adaptation; validation is recorded in this unit's CI receipts.
Exact replacement candidate for the current original leaf.
Heights reference source bodies are ported independently into local namespaces.
-/
import Solutions.Source_FermatPolarPresentationHeights
import Solutions.Source_FermatPolarIntegrality

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- Exact current statement, preserving all arbitrary supplied presentations. -/
theorem polarPresentationHeightSum_of_principalRelation {N : ℕ}
    (M : Model N) (hDVR : PlacesDiscrete M) (hRF : ResiduesFinite M)
    (D E : Divisor M) (RD : PolarPresentation M hDVR D)
    (RE : PolarPresentation M hDVR E) (f r : M.K) (hr : r ≠ 0)
    (hrel : ∀ P : Place M.K,
      D P + E P = poleMultiplicity M hDVR f P + ord M hDVR P r) :
    ∃ C : ℝ, ∀ x : QbarPoint M.K,
      |divHeight RD x + divHeight RE x - functionHeight M f x| ≤ C := by
  have hMono : PolarTupleHeightMonotonicity := by
    intro K _ _ _ ι κ _ _ s t hs ht hle
    exact PolarTuple.tupleHeight_le_of_minOrd_le hs ht hle
  exact polarPresentationHeightSum_of_tupleMonotonicity hMono
    M hDVR hRF D E RD RE f r hr hrel

end AbcAdaptation.Tripod.Fermat.Proper
