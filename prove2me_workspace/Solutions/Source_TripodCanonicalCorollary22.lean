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

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut

variable {AG : AnabelianGeometry.{0}} {TG : TemperedGeometry AG}

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
  intro d hd K
  let CI := curveInputs_from_source P K d (CF K d) (hcore K d) northcottHyp
    (legendreHeight P K) (twoAdicBound P K)
  let I := CI.toCorollary22Inputs
  have ex : ConcreteThetaDataExistence.{0, 0} (AG := AG) (TG := TG) I :=
    concreteThetaDataExistence_from_source P K d (CF K d) (hcore K d) northcottHyp anab
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
  have hEstimate := I.c2 (P := IsConcrete) hd ex.toThetaDataExistence cheb pnt
    (fun _ ⟨D, LT, TL, QI, hX⟩ => hX ▸ h312 D LT TL QI) x hx hxe hH
  rw [hheight] at hEstimate
  exact hEstimate

end AbcAdaptation.Tripod
