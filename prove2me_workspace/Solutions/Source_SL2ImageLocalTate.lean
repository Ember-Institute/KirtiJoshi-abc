/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Concrete/Existence.lean and Iut/Concrete/SL2Image.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants
import Solutions.Source_ReferenceIutSplitSquare
import Solutions.Source_ReferenceIutTateStructureOfTorsion
import Solutions.Source_ReferenceIutTateUniformizationLaws
import Solutions.Source_SL2ImageLocalTorsion

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.EllipticCurveData

open NumberField
open scoped Classical Valued

universe u

noncomputable section

section BadPlaces

variable (C : EllipticCurveData.{u}) (CA : C.CurveArithmetic) {ℓ : ℕ}

include CA in
/-- The pullback of the selected bad places is the multiplicative locus away from `2` and `ℓ`. -/
lemma badPlacesOver_VBadOf :
    badPlacesOver C.F C.E (C.VBadOf ℓ) =
      {w | w ∈ C.badAll ∧ residueChar w ≠ 2 ∧ residueChar w ≠ ℓ} := by
  ext w
  constructor
  · rintro ⟨v, ⟨h2, hℓ, -, hmult⟩, hwv⟩
    refine ⟨hmult w hwv, ?_, ?_⟩ <;> rw [CA.residueChar_liesOver v w hwv] <;> assumption
  · rintro ⟨hw, h2, hℓ⟩
    obtain ⟨v, hwv⟩ := CA.exists_liesOver w
    have hres := CA.residueChar_liesOver v w hwv
    have hv2 : residueChar v ≠ 2 := by rwa [← hres]
    have hvℓ : residueChar v ≠ ℓ := by rwa [← hres]
    refine ⟨v, ⟨hv2, hvℓ, ⟨w, hwv⟩, ?_⟩, hwv⟩
    exact fun w₀ hw₀ => CA.mult_invariant v hv2 w w₀ hwv hw₀ hw

variable (R : C.ModEllRepData ℓ)

include CA in
private theorem torsionField_isBadPlace_of_liesOver
    {w : FinitePlace C.F} (hw : w ∈ C.badAll)
    (h2 : residueChar w ≠ 2) (hwℓ : residueChar w ≠ ℓ)
    {w' : FinitePlace ↥R.torsionField} (hw'w : FinitePlace.LiesOver w' w) :
    IsBadPlace C.E R.torsionField (C.VBadOf ℓ) w' := by
  have hmem : w ∈ badPlacesOver C.F C.E (C.VBadOf ℓ) := by
    rw [C.badPlacesOver_VBadOf CA]
    exact ⟨hw, h2, hwℓ⟩
  obtain ⟨v, hv, hwv⟩ := hmem
  let K := R.torsionField
  letI : Algebra ↥(fieldOfModuli C.F C.E) ↥K :=
    (fieldOfModuli C.F C.E).instAlgebraSubtypeMem
  have hmap : algebraMap ↥(fieldOfModuli C.F C.E) ↥K =
      (algebraMap C.F ↥K).comp (algebraMap ↥(fieldOfModuli C.F C.E) C.F) :=
    RingHom.ext fun _ => rfl
  letI : IsScalarTower ↥(fieldOfModuli C.F C.E) C.F ↥K :=
    IsScalarTower.of_algebraMap_eq' hmap
  letI : IsScalarTower (𝓞 ↥(fieldOfModuli C.F C.E)) (𝓞 C.F) (𝓞 ↥K) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      apply RingOfIntegers.coe_injective
      exact RingHom.congr_fun hmap x)
  haveI : w'.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hw'w
  haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hwv
  exact ⟨v, hv, ⟨(Ideal.LiesOver.trans w'.maximalIdeal.asIdeal
    w.maximalIdeal.asIdeal v.maximalIdeal.asIdeal).over⟩⟩

end BadPlaces

/-- The prime divides the relative ramification index above a multiplicative place
whose Tate order is prime to it and whose residue characteristic differs from `2` and `ℓ`. -/
theorem prime_dvd_ramificationIdx_from_source
    (C : EllipticCurveData.{u}) (CA : C.CurveArithmetic)
    (TI : C.TateInputs) {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) (R : C.ModEllRepData ℓ)
    {w : FinitePlace C.F} (hw : w ∈ C.badAll)
    (h2 : residueChar w ≠ 2) (hwℓ : residueChar w ≠ ℓ) (hP2 : ¬ ℓ ∣ TI.qOrder w hw)
    {w' : FinitePlace ↥R.torsionField} (hw'w : FinitePlace.LiesOver w' w) :
    ℓ ∣ w.maximalIdeal.asIdeal.ramificationIdx' w'.maximalIdeal.asIdeal := by
  have hbad := C.torsionField_isBadPlace_of_liesOver CA R hw h2 hwℓ hw'w
  let S : TateStructure (curveKw C.E R.torsionField w') :=
    tateStructureOfBadPlace C.E R.torsionField (VBad := C.VBadOf ℓ) (w := w')
      (fun _ hv => hv.1) (fun _ hv w₀ hw₀ => hv.2.2.2 w₀ hw₀) hbad
      (exists_sq_eq_neg_c₄_mul_c₆ C.E R.torsionField (VBad := C.VBadOf ℓ)
        (fun _ hv => hv.1) (fun _ hv w₀ hw₀ => hv.2.2.2 w₀ hw₀)
        hℓ hodd R.TK le_rfl (by rw [R.card_torsionBy_EK, sq]) hbad)
      TateParameterUniformization.ofTateParameter
  exact C.prime_dvd_ramificationIdx_of_tateStructure R TI hℓ hw hP2 hw'w S

end

end AbcAdaptation.Reference.Iut.EllipticCurveData
