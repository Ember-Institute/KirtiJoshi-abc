/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Concrete/SL2Image.lean (prime_dvd_card_range)
-/
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_ModEllRepTorsionField
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Ideal.GoingUp
import Theorems.Thm_AbcAdaptation_Reference_Iut_EllipticCurveData_prime_dvd_ramificationIdx

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Concrete/ModEllRepGalois.lean
-/

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.EllipticCurveData.ModEllRepData

open WeierstrassCurve Matrix
open scoped Classical

universe u

noncomputable section

variable {C : EllipticCurveData.{u}} {ℓ : ℕ} (R : C.ModEllRepData ℓ)

/-- The fixed field of the normal subgroup `ker ρ` is Galois over `F`. -/
instance isGalois_torsionField : IsGalois C.F ↥R.torsionField :=
  IsGalois.of_fixedField_normal_subgroup R.rep.ker

lemma fixingSubgroup_torsionField : R.torsionField.fixingSubgroup = R.rep.ker :=
  InfiniteGalois.fixingSubgroup_fixedField (k := C.F) (K := C.Fbar)
    ⟨R.rep.ker, Subgroup.isClosed_of_isOpen _ R.ker_isOpen⟩

lemma restrictNormalHom_ker_eq :
    (AlgEquiv.restrictNormalHom R.torsionField :
      (C.Fbar ≃ₐ[C.F] C.Fbar) →* (↥R.torsionField ≃ₐ[C.F] ↥R.torsionField)).ker = R.rep.ker := by
  rw [IntermediateField.restrictNormalHom_ker, R.fixingSubgroup_torsionField]

/-- The representation image and the Galois group of `K/F` are both quotients by `ker ρ`. -/
def rangeEquivGal : R.rep.range ≃* (↥R.torsionField ≃ₐ[C.F] ↥R.torsionField) :=
  (QuotientGroup.quotientKerEquivRange R.rep).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq R.restrictNormalHom_ker_eq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        (AlgEquiv.restrictNormalHom_surjective (F := C.F) (K₁ := ↥R.torsionField)
          (E := C.Fbar))))

lemma card_range : Nat.card R.rep.range = Nat.card (↥R.torsionField ≃ₐ[C.F] ↥R.torsionField) :=
  Nat.card_congr R.rangeEquivGal.toEquiv

end

end AbcAdaptation.Reference.Iut.EllipticCurveData.ModEllRepData

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Concrete/SL2Image.lean and Iut/Cor312/ThetaData/PlacesOver.lean
-/

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain

section Places

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- Every finite place of the base field has a finite place above it. -/
theorem FinitePlace.exists_liesOver (v : FinitePlace k) :
    ∃ w : FinitePlace K, FinitePlace.LiesOver w v := by
  haveI : v.maximalIdeal.asIdeal.IsPrime := v.maximalIdeal.isPrime
  obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K)
    v.maximalIdeal.asIdeal ⊥ (by
      simpa only [Ideal.under_bot] using
        (bot_le : (⊥ : Ideal (𝓞 k)) ≤ v.maximalIdeal.asIdeal))
  have hQne : Q ≠ ⊥ := by
    rintro rfl
    change (⊥ : Ideal (𝓞 K)).under (𝓞 k) = v.maximalIdeal.asIdeal at hQv
    rw [Ideal.under_bot] at hQv
    exact v.maximalIdeal.ne_bot hQv.symm
  refine ⟨FinitePlace.mk ⟨Q, hQ, hQne⟩, ?_⟩
  unfold FinitePlace.LiesOver
  rw [FinitePlace.maximalIdeal_mk]
  exact ⟨hQv.symm⟩

end Places

namespace EllipticCurveData

open IsDedekindDomain.HeightOneSpectrum

universe u

variable (C : EllipticCurveData.{u}) {ℓ : ℕ} (R : C.ModEllRepData ℓ)

/-- The relative ramification index divides the order of the torsion field's Galois group. -/
lemma ramificationIdx'_dvd_card_gal
    {w : FinitePlace C.F} {w' : FinitePlace ↥R.torsionField}
    (hw'w : FinitePlace.LiesOver w' w) :
    w.maximalIdeal.asIdeal.ramificationIdx' w'.maximalIdeal.asIdeal ∣
      Nat.card (↥R.torsionField ≃ₐ[C.F] ↥R.torsionField) := by
  haveI : w'.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hw'w
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    w.maximalIdeal.asIdeal (𝓞 ↥R.torsionField) (↥R.torsionField ≃ₐ[C.F] ↥R.torsionField)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ w'.maximalIdeal.asIdeal
    (↥R.torsionField ≃ₐ[C.F] ↥R.torsionField)] at h
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ w.maximalIdeal.ne_bot]
  refine ⟨(w.maximalIdeal.asIdeal.primesOver (𝓞 ↥R.torsionField)).ncard *
    w.maximalIdeal.asIdeal.inertiaDegIn (𝓞 ↥R.torsionField), ?_⟩
  rw [← h]
  exact Nat.mul_left_comm _ _ _

/-- The local ramification divisibility at a place from (P5) gives the image divisibility. -/
theorem prime_dvd_card_range_of_ramification (TI : C.TateInputs)
    (hRamification : ∀ {w : FinitePlace C.F} (hw : w ∈ C.badAll),
      residueChar w ≠ 2 → residueChar w ≠ ℓ → (¬ ℓ ∣ TI.qOrder w hw) →
      ∀ {w' : FinitePlace ↥R.torsionField}, FinitePlace.LiesOver w' w →
        ℓ ∣ w.maximalIdeal.asIdeal.ramificationIdx' w'.maximalIdeal.asIdeal)
    (hP2 : ∀ w (hw : w ∈ C.badAll), ¬ ℓ ∣ TI.qOrder w hw)
    (hP5 : ∃ w ∈ C.badAll, residueChar w ≠ 2 ∧ residueChar w ≠ ℓ) :
    ℓ ∣ Nat.card R.rep.range := by
  obtain ⟨w, hw, h2, hwℓ⟩ := hP5
  obtain ⟨w', hw'w⟩ := FinitePlace.exists_liesOver (K := ↥R.torsionField) w
  rw [R.card_range]
  exact (hRamification hw h2 hwℓ (hP2 w hw) hw'w).trans
    (C.ramificationIdx'_dvd_card_gal R hw'w)

end EllipticCurveData

end AbcAdaptation.Reference.Iut

set_option autoImplicit false

open AbcAdaptation.Reference.Iut

universe u

theorem solution (C : EllipticCurveData.{u}) (CA : C.CurveArithmetic)
    (TI : C.TateInputs) {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) (R : C.ModEllRepData ℓ)
    (hP2 : ∀ w (hw : w ∈ C.badAll), ¬ ℓ ∣ TI.qOrder w hw)
    (hP5 : ∃ w ∈ C.badAll, residueChar w ≠ 2 ∧ residueChar w ≠ ℓ) :
    ℓ ∣ Nat.card R.rep.range :=
  C.prime_dvd_card_range_of_ramification R TI
    (fun {w} hw h2 hwℓ hcop {w'} hw'w =>
      C.prime_dvd_ramificationIdx CA TI hℓ hodd R (w := w) hw h2 hwℓ hcop (w' := w') hw'w)
    hP2 hP5
