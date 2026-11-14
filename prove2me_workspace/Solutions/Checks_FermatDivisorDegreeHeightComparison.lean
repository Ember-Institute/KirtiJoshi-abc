/- Exact source and consumer acceptance checks. -/
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_divisorDegreeHeightComparison

set_option autoImplicit false
open AbcAdaptation.Tripod.Fermat.Proper

#print axioms positiveDegreePolarRealization
#print axioms PolarTuple.abs_tupleHeight_sub_sub_le
#print axioms DegreeHeightMachine.chosenHeight_approx
#print axioms DegreeHeightMachine.chosenHeight_bddBelow
#print axioms DegreeHeightMachine.chosenHeight_le_mul
#print axioms suppliedPresentationHeight_approx_chosen
#print axioms divisorDegreeHeightComparison

/-- Exact signature of the real canonicalEstimate_of_belyi_children consumer.
Every point remains a full proper algebraic point; no affine or good-value filter. -/
example {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M) (hRF : ResiduesFinite M)
    (D E : Divisor M) (RD : PolarPresentation M hDVR D)
    (RE : PolarPresentation M hDVR E) (q : ℝ)
    (hpos : 0 < divisorDegree M D)
    (hstrict : (divisorDegree M E : ℝ) < q * divisorDegree M D) :
    ∃ C : ℝ, ∀ x : QbarPoint M.K,
      divHeight RE x ≤ q * divHeight RD x + C :=
  divisorDegreeHeightComparison M hDVR hRF D E RD RE q hpos hstrict
