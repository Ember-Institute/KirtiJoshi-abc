/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Concrete/CurveArithmeticProved.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_CurveArithmetic
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_GoodReductionHeight
import Solutions.Source_TripodFinitePrimeCounting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutCompat.Cor312.ThetaData.ValuationTransfer
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBadPlaceFiniteness
import ArithmeticTeichmullerSpaces.Prologue.Arithmetic.Basic
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.PlaceUnder

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.EllipticCurveData

open NumberField

universe u

/-- Assemble the curve arithmetic from its four curve-specific inputs. -/
theorem CurveArithmetic.ofCore (C : EllipticCurveData.{u}) (h1 : IsSquare (-1 : C.F))
    (h2 : ∀ w : FinitePlace C.F, HasStableReductionAt C.E w)
    (h3 : SixTorsionRational C.F C.E C.Fbar)
    (h4 : ∀ ℓ : ℕ, ℓ.Prime → 7 ≤ ℓ → IsGaloisOfDegreePrimeTo C.F C.E ℓ) :
    C.CurveArithmetic := by
  have hBad : C.badAll.Finite := by
    change {w : FinitePlace C.F | JoshiTeich.ReferenceIut.HasMultiplicativeReductionAt C.E w}.Finite
    exact JoshiTeich.Act1Scene1.multiplicativeReductionPlaces_finite C.E
  refine
    { sqrt_neg_one := h1
      stable_reduction := h2
      six_torsion_rational := h3
      galois_deg_prime := h4
      exists_liesOver := fun w =>
        ⟨JoshiTeich.ReferenceIut.placeUnder w, JoshiTeich.ReferenceIut.liesOver_placeUnder w⟩
      residueChar_liesOver := fun _ _ hw =>
        JoshiTeich.Prologue.Arithmetic.residueChar_eq_of_liesOver hw
      mult_invariant := ?_
      badAll_finite := hBad
      inertDeg_pos := fun w => Ideal.inertiaDeg_pos w.maximalIdeal.asIdeal ℤ
      sum_inertDeg_le := fun q => AbcAdaptation.Tripod.sum_inertDeg_filter_le hBad.toFinset q }
  intro v _ w w' hw hw' hMult
  let jMod : ↥(fieldOfModuli C.F C.E) := ⟨C.E.j, IntermediateField.mem_adjoin_simple_self ℚ C.E.j⟩
  have integralIff (u : FinitePlace C.F) (hu : FinitePlace.LiesOver u v) :
      u.maximalIdeal.valuation C.F C.E.j ≤ 1 ↔ v.maximalIdeal.valuation _ jMod ≤ 1 := by
    change u.maximalIdeal.valuation C.F (algebraMap _ C.F jMod) ≤ 1 ↔ _
    exact JoshiTeich.ReferenceIut.valuation_algebraMap_le_one_iff hu jMod
  apply (hasMultiplicativeReductionAt_iff_of_stable C.E w' (h2 w')).mpr
  intro hj'
  exact (hasMultiplicativeReductionAt_iff_of_stable C.E w (h2 w)).mp hMult
    ((integralIff w hw).mpr ((integralIff w' hw').mp hj'))

end AbcAdaptation.Reference.Iut.EllipticCurveData
