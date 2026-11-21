/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Implication/Corollary22.lean and Iut/Implication/Corollary23.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_TwoAdicBound
import Definitions.Def_TripodCanonicalHighHeightComposition
import Definitions.Def_TripodStatementIIComposition
import Solutions.Source_ReferenceIutChebyshevExplicit
import Solutions.Source_ReferenceIutPrimeCountingExplicit
import Solutions.Source_TripodCurveInputsFromSource
import Solutions.Source_TripodProviderLegendreComparison
import Theorems.Thm_AbcAdaptation_Reference_Iut_Corollary22Inputs_c2
import Theorems.Thm_AbcAdaptation_Tripod_boundedDegreeFiniteness
import Theorems.Thm_AbcAdaptation_Tripod_epsilonELargeHeight

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut

variable {AG : AnabelianGeometry.{0}} {TG : TemperedGeometry AG}

/-- The canonical Corollary 2.2 estimate from P7 and the variant above a prime bound
uniform over the points of each bounded-degree compactly bounded family. -/
theorem canonicalCorollary22HighHeightEstimate_of_thetaDataExistenceAtLeast
    (P : CurveProviders) {TK : CompactlyBounded → ℝ}
    (CF : ∀ K d, CurveFactsProp P K d (TK K))
    (hcore : ∀ K d, CoreFinitenessHyp P K d AG)
    (cheb : ChebyshevBound) (pnt : PrimeCountingBound)
    (minimum : CompactlyBounded → ℕ → ℕ)
    (dataPredicate : CompactlyBounded → ℕ → Corollary312VariantData.{0, 0} AG TG → Prop)
    (ex : ∀ K d, ThetaDataExistenceAtLeast (minimum K d) (dataPredicate K d)
      (curveInputs_from_source P K d (CF K d) (hcore K d) northcottHyp
        (legendreHeight P K) (twoAdicBound P K)).toCorollary22Inputs)
    (h312 : ∀ K d X, dataPredicate K d X → minimum K d ≤ X.ℓ → Corollary312Variant X) :
    CanonicalCorollary22HighHeightEstimate := by
  intro d hd K
  let CI := curveInputs_from_source P K d (CF K d) (hcore K d) northcottHyp
    (legendreHeight P K) (twoAdicBound P K)
  let I := CI.toCorollary22Inputs
  let E : Set Pt :=
    (I.excCore ∩ (tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d)) ∪
      {x | x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d ∧
        I.h x ≤ (minimum K d : ℝ) ^ 2}
  have hE : E.Finite := I.excCore_finite.union (I.northcott ((minimum K d : ℝ) ^ 2))
  refine ⟨E, I.threshold cheb, 40 * pnt.η + I.B / 3, hE, ?_⟩
  intro x hxK hxd hxE hxH
  have hx : x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d :=
    ⟨hxK, mem_ptLE.mpr hxd⟩
  have hxe : x ∉ I.excCore := fun h => hxE (Or.inl ⟨h, hx⟩)
  have hHeightCutoff : (minimum K d : ℝ) ^ 2 < I.h x := by
    apply lt_of_not_ge
    intro h
    exact hxE (Or.inr ⟨hx, h⟩)
  have hMinimum : (minimum K d : ℝ) ≤ Real.sqrt (I.h x) :=
    Real.le_sqrt_of_sq_le hHeightCutoff.le
  have hheight : I.h x = auxiliaryHeight x := providerHeight_eq_auxiliaryHeight P x
  have hH : I.threshold cheb ≤ I.h x := by
    rw [hheight]
    exact hxH
  have hEstimate := I.c2_of_prime_lower_bound hd (ex K d) cheb pnt (h312 K d)
    x hx hxe hH hMinimum
  rw [hheight] at hEstimate
  exact hEstimate

/-- The existing StatementII composition applied to P7 above a supplied prime bound. -/
theorem statementII_of_thetaDataExistenceAtLeast
    (P : CurveProviders) {TK : CompactlyBounded → ℝ}
    (CF : ∀ K d, CurveFactsProp P K d (TK K))
    (hcore : ∀ K d, CoreFinitenessHyp P K d AG)
    (minimum : CompactlyBounded → ℕ → ℕ)
    (dataPredicate : CompactlyBounded → ℕ → Corollary312VariantData.{0, 0} AG TG → Prop)
    (ex : ∀ K d, ThetaDataExistenceAtLeast (minimum K d) (dataPredicate K d)
      (curveInputs_from_source P K d (CF K d) (hcore K d) northcottHyp
        (legendreHeight P K) (twoAdicBound P K)).toCorollary22Inputs)
    (h312 : ∀ K d X, dataPredicate K d X → minimum K d ≤ X.ℓ → Corollary312Variant X) :
    StatementII :=
  statementII_of_children boundedDegreeFiniteness
    (highHeightEstimate_of_canonical_children
      (canonicalLegendreHeightComparison_of_provider P)
      (canonicalCorollary22HighHeightEstimate_of_thetaDataExistenceAtLeast P CF hcore
        chebyshevBoundExplicit primeCountingBoundExplicit minimum dataPredicate ex h312)
      epsilonELargeHeight)

end AbcAdaptation.Tripod
