/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Concrete/Main.lean, Iut/Implication/Corollary23.lean
and Iut/Tripod/Main.lean
-/
import Solutions.Source_TripodP7
import Solutions.Source_TripodProviderAuxiliaryHeight
import Theorems.Thm_AbcAdaptation_Reference_Iut_Corollary22Inputs_c2
import Theorems.Thm_AbcAdaptation_Tripod_cyclicBoundOdd

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut

variable {AG : AnabelianGeometry.{0}} {TG : TemperedGeometry AG}

private theorem canonicalCorollary22HighHeightEstimate_of_thetaDataExistence
    (P : CurveProviders) {TK : CompactlyBounded → ℝ}
    (CF : ∀ K d, CurveFactsProp P K d (TK K))
    (hcore : ∀ K d, CoreFinitenessHyp P K d AG)
    (cheb : ChebyshevBound) (pnt : PrimeCountingBound)
    (dataPredicate : CompactlyBounded → ℕ → Corollary312VariantData.{0, 0} AG TG → Prop)
    (ex : ∀ K d, ThetaDataExistence (dataPredicate K d)
      (curveInputs_from_source P K d (CF K d) (hcore K d) northcottHyp
        (legendreHeight P K) (twoAdicBound P K)).toCorollary22Inputs)
    (h312 : ∀ K d X, dataPredicate K d X → Corollary312Variant X) :
    CanonicalCorollary22HighHeightEstimate := by
  intro d hd K
  let CI := curveInputs_from_source P K d (CF K d) (hcore K d) northcottHyp
    (legendreHeight P K) (twoAdicBound P K)
  let I := CI.toCorollary22Inputs
  let E : Set Pt := I.excCore ∩ (tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d)
  refine ⟨E, I.threshold cheb, 40 * pnt.η + I.B / 3, I.excCore_finite, ?_⟩
  intro x hxK hxd hxE hxH
  have hx : x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d :=
    ⟨hxK, mem_ptLE.mpr hxd⟩
  have hxe : x ∉ I.excCore := fun h => hxE ⟨h, hx⟩
  have hheight : I.h x = auxiliaryHeight x := providerHeight_eq_auxiliaryHeight P x
  have hH : I.threshold cheb ≤ I.h x := by
    rw [hheight]
    exact hxH
  have hEstimate := I.c2 hd (ex K d) cheb pnt (h312 K d) x hx hxe hH
  rw [hheight] at hEstimate
  exact hEstimate

/-- The reference Corollary 2.2 conclusion on the actual tripod, with the fixed
auxiliary height and the concrete initial data from the Legendre curves. -/
theorem canonicalCorollary22HighHeightEstimate_of_source
    (P : CurveProviders) {TK : CompactlyBounded → ℝ}
    (CF : ∀ K d, CurveFactsProp P K d (TK K))
    (hcore : ∀ K d, CoreFinitenessHyp P K d AG)
    (anab : AnabelianExistence AG TG) (cheb : ChebyshevBound) (pnt : PrimeCountingBound)
    (h312 : ∀ (D : InitialThetaData AG TG) (LT : LocalTheory.{0, 0} D.Kt)
      (TL : ThetaLocalData D LT) (QI : QPilotInputs D),
      Corollary312Variant (concreteVariantData D LT TL QI)) :
    CanonicalCorollary22HighHeightEstimate := by
  exact canonicalCorollary22HighHeightEstimate_of_thetaDataExistence P CF hcore cheb pnt
    (fun _ _ => IsConcrete)
    (fun K d =>
      (concreteThetaDataExistence_from_source P K d (CF K d) (hcore K d)
        northcottHyp anab).toThetaDataExistence)
    (fun _ _ _ ⟨D, LT, TL, QI, hX⟩ => hX ▸ h312 D LT TL QI)

/-- Corollary 2.2 from the variant on the bundles produced by the source (P7). -/
theorem canonicalCorollary22HighHeightEstimate_of_sourceP7
    (P : CurveProviders) {TK : CompactlyBounded → ℝ}
    (CF : ∀ K d, CurveFactsProp P K d (TK K))
    (hcore : ∀ K d, CoreFinitenessHyp P K d AG)
    (anab : AnabelianExistence AG TG) (cheb : ChebyshevBound) (pnt : PrimeCountingBound)
    (h312 : ∀ (K : CompactlyBounded) (d : ℕ) (X : Corollary312VariantData.{0, 0} AG TG),
      let CI := curveInputs_from_source P K d (CF K d) (hcore K d) northcottHyp
        (legendreHeight P K) (twoAdicBound P K)
      IsSourceP7Variant CI anab X → Corollary312Variant X) :
    CanonicalCorollary22HighHeightEstimate :=
  canonicalCorollary22HighHeightEstimate_of_thetaDataExistence P CF hcore cheb pnt
    (fun K d => IsSourceP7Variant
      (curveInputs_from_source P K d (CF K d) (hcore K d) northcottHyp
        (legendreHeight P K) (twoAdicBound P K)) anab)
    (fun K d => pointThetaDataExistence_from_source P K d (CF K d) (hcore K d) northcottHyp anab)
    h312

/-- The canonical Corollary 2.2 estimate with the cyclic bound supplied by the
Vélu estimates and the complex torsion bound. -/
theorem canonicalCorollary22HighHeightEstimate_of_cyclicBound
    (P : CurveProviders)
    (hcore : ∀ K d, CoreFinitenessHyp P K d AG)
    (anab : AnabelianExistence AG TG) (cheb : ChebyshevBound) (pnt : PrimeCountingBound)
    (h312 : ∀ (D : InitialThetaData AG TG) (LT : LocalTheory.{0, 0} D.Kt)
      (TL : ThetaLocalData D LT) (QI : QPilotInputs D),
      Corollary312Variant (concreteVariantData D LT TL QI)) :
    CanonicalCorollary22HighHeightEstimate :=
  canonicalCorollary22HighHeightEstimate_of_source P
    (TK := fun K => cyclicConst K (torsionConst K.c (legendre_torsion_x_le K.c)))
    (fun K d => ⟨cyclicBoundOdd P K d⟩) hcore anab cheb pnt h312

end AbcAdaptation.Tripod
