import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBaseSixthRoot
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadOrdinaryLogAbsorption
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOrdinaryLogGlobalMargin

/-!
source-id: JT-SCENE1-ACTUAL-MODULI-RAMIFICATION-ABSORPTION
source: actual VBad ell-divisible relative ramification, base Tate sixth
root and the base/moduli local degree tower; Joshi III 3520--3574, 3624--3631.
fidelity: retaining the base/moduli ramification factor replaces the
base ramification <=2 sufficient condition by moduli ramification <=2.
The original base completion may have arbitrarily large ramification.
The condition on the moduli place and the complementary local tests stay
explicit; no unconditional global margin or paper theta identity is asserted.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
open JoshiTeich.Prologue
open scoped Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance moduliAbsorptionPrime (v : iutInitialThetaOddModSupportFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩

private theorem localDeg_ge_relativeRamIdx_mul
    {F K : Type u} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    {w : NumberField.FinitePlace F} {z : NumberField.FinitePlace K}
    (hzw : Ideal.LiesOver z.maximalIdeal.asIdeal w.maximalIdeal.asIdeal) :
    Arithmetic.relRamIdx z w * Arithmetic.localDeg w ≤ Arithmetic.localDeg z := by
  have hd := Arithmetic.localDeg_eq_mul hzw
  have hp : 0 < Arithmetic.relRamIdx z w * Arithmetic.relInertDeg z w :=
    Nat.pos_of_mul_pos_left (hd ▸ Arithmetic.localDeg_pos z)
  have hf : 1 ≤ Arithmetic.relInertDeg z w := Nat.pos_of_mul_pos_left hp
  calc
    _ = Arithmetic.localDeg w * (Arithmetic.relRamIdx z w * 1) := by ring
    _ ≤ Arithmetic.localDeg w * (Arithmetic.relRamIdx z w * Arithmetic.relInertDeg z w) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hf)
    _ = _ := hd.symm

private theorem selectedBase_liesOver_moduli
    (v : iutInitialThetaOddModSupportFinset D) :
    Ideal.LiesOver
      ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace
        (FullSupportPaperWeightedHull.selected D v)).1.maximalIdeal.asIdeal
      v.1.maximalIdeal.asIdeal := by
  have hb : ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace
      (FullSupportPaperWeightedHull.selected D v)).1 = iutInitialThetaSectionBasePlace D v.1 :=
    iutInitialThetaOddSupportSelectedQRootPlace_basePlace_eq_sectionBasePlace D v.1
      ((iutInitialThetaOddModSupport_finite D).mem_toFinset.mp v.2)
  rw [hb]
  exact iutInitialThetaSectionBasePlace_liesOver D v.1

theorem vbad_source_localDeg_ge_ell_mul_base
    (v : iutInitialThetaOddModSupportFinset D) (hv : v.1 ∈ D.VBad) :
    D.prime.ℓ * Arithmetic.localDeg
        ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace
          (FullSupportPaperWeightedHull.selected D v)).1 ≤
      Arithmetic.localDeg (FullSupportPaperWeightedHull.selected D v).1 := by
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let s := FullSupportPaperWeightedHull.selected D v
  let b := R.basePlace s
  have hw : b.1 ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad :=
    ⟨v.1, hv, selectedBase_liesOver_moduli D v⟩
  have hdiv := iutInitialThetaEll_dvd_qRootRelativeRamIdx_on_vbad D s hw
  have hell : D.prime.ℓ ≤ Arithmetic.relRamIdx s.1 b.1 :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Arithmetic.relRamIdx_ne_zero (R.liesOver s))) hdiv
  exact (Nat.mul_le_mul_right _ hell).trans (localDeg_ge_relativeRamIdx_mul (R.liesOver s))

theorem vbad_source_localDeg_ge_ell_mul_baseRelativeRamIdx
    (v : iutInitialThetaOddModSupportFinset D) (hv : v.1 ∈ D.VBad) :
    (D.prime.ℓ * Arithmetic.relRamIdx
      ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace
        (FullSupportPaperWeightedHull.selected D v)).1 v.1) * Arithmetic.localDeg v.1 ≤
      Arithmetic.localDeg (FullSupportPaperWeightedHull.selected D v).1 := by
  calc
    _ = D.prime.ℓ * (Arithmetic.relRamIdx _ v.1 * Arithmetic.localDeg v.1) := by ring
    _ ≤ D.prime.ℓ * Arithmetic.localDeg
        ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace
          (FullSupportPaperWeightedHull.selected D v)).1 :=
      Nat.mul_le_mul_left _ (localDeg_ge_relativeRamIdx_mul (selectedBase_liesOver_moduli D v))
    _ ≤ _ := vbad_source_localDeg_ge_ell_mul_base D v hv

theorem arithmeticAbsorption_on_vbad_of_moduli_ramIdx_le_two
    (v : iutInitialThetaOddModSupportFinset D) (hv : v.1 ∈ D.VBad)
    (he : Arithmetic.ramIdx v.1 ≤ 2) : arithmeticAbsorption D v := by
  let b := (iutInitialThetaOddSupportTorsionQRootSource D).basePlace
    (FullSupportPaperWeightedHull.selected D v)
  let t := D.prime.ℓ * Arithmetic.relRamIdx b.1 v.1
  have hb := selectedBase_liesOver_moduli D v
  have hr : 1 ≤ Arithmetic.relRamIdx b.1 v.1 :=
    Nat.one_le_iff_ne_zero.mpr (Arithmetic.relRamIdx_ne_zero hb)
  have ht : 5 ≤ t := D.prime.five_le.trans (by
    simpa only [mul_one] using Nat.mul_le_mul_left D.prime.ℓ hr)
  have hT : sourceThreshold D v = 2 * Arithmetic.ramIdx v.1 * t := by
    change 2 * D.prime.ℓ * Arithmetic.ramIdx b.1 = _
    rw [Arithmetic.ramIdx_eq_mul hb]
    dsimp only [t]
    ring
  have hq : 6 ≤ sourceQOrder D v := baseTateParameter_qOrder_ge_six D _
  have hsum : sourceThreshold D v + sourceQOrder D v ≤ t * sourceQOrder D v := by
    rw [hT]
    calc
      _ ≤ 4 * t + sourceQOrder D v := by
        exact Nat.add_le_add_right (by simpa using Nat.mul_le_mul_right t (Nat.mul_le_mul_left 2 he)) _
      _ ≤ (t - 1) * 6 + sourceQOrder D v := by omega
      _ ≤ (t - 1) * sourceQOrder D v + sourceQOrder D v :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hq) _
      _ = t * sourceQOrder D v := by
        rw [← Nat.add_one_mul, Nat.sub_add_cancel (show 1 ≤ t by omega)]
  unfold arithmeticAbsorption
  calc
    _ ≤ Arithmetic.localDeg v.1 * (t * sourceQOrder D v) := Nat.mul_le_mul_left _ hsum
    _ = (t * Arithmetic.localDeg v.1) * sourceQOrder D v := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (vbad_source_localDeg_ge_ell_mul_baseRelativeRamIdx D v hv)

theorem correctedLocalCost_le_paperTerm_on_vbad_of_moduli_ramIdx_le_two
    (v : iutInitialThetaOddModSupportFinset D) (hv : v.1 ∈ D.VBad)
    (he : Arithmetic.ramIdx v.1 ≤ 2) : correctedLocalCost D v ≤ selectedPaperTerm D v :=
  (correctedLocalCost_le_paperTerm_iff_arithmetic D v).mpr
    (arithmeticAbsorption_on_vbad_of_moduli_ramIdx_le_two D v hv he)

theorem correctedCost_le_selectedPaperSum_of_moduli_low_ramification
    (he : ∀ v : iutInitialThetaOddModSupportFinset D, v.1 ∈ D.VBad → Arithmetic.ramIdx v.1 ≤ 2)
    (hother : ∀ v : iutInitialThetaOddModSupportFinset D, v.1 ∉ D.VBad → arithmeticAbsorption D v) :
    FullSupportPaperWeightedHull.weightedPaperSum D - Real.log (correction D 1) ≤
      iutInitialThetaSelectedQRootPaperSum D := by
  apply correctedCost_le_selectedPaperSum_of_arithmetic D
  intro v
  by_cases hv : v.1 ∈ D.VBad
  · exact arithmeticAbsorption_on_vbad_of_moduli_ramIdx_le_two D v hv (he v hv)
  · exact hother v hv

theorem globalArithmeticMargin_nonneg_of_moduli_low_ramification
    (he : ∀ v : iutInitialThetaOddModSupportFinset D, v.1 ∈ D.VBad → Arithmetic.ramIdx v.1 ≤ 2)
    (hother : ∀ v : iutInitialThetaOddModSupportFinset D, v.1 ∉ D.VBad → arithmeticAbsorption D v) :
    0 ≤ globalArithmeticMargin D :=
  (globalArithmeticMargin_nonneg_iff D).mpr
    (correctedCost_le_selectedPaperSum_of_moduli_low_ramification D he hother)

variable (n : ℕ) {κ : Type*}
variable (C : ∀ v : iutInitialThetaOddModSupportFinset D, κ → Set (packet D n v).Tensor)
variable (hw : ∀ v, witness D n v ∈ ⋃ k, C v k)
variable (hunit : ∀ v k, C v k ⊆ (packet D n v).normalization)

include hw hunit in
theorem ordinary_collation_averageAbsLog_le_selectedPaperSum_of_moduli_low_ramification
    (hn : 0 < n)
    (he : ∀ v : iutInitialThetaOddModSupportFinset D, v.1 ∈ D.VBad → Arithmetic.ramIdx v.1 ≤ 2)
    (hother : ∀ v : iutInitialThetaOddModSupportFinset D, v.1 ∉ D.VBad → arithmeticAbsorption D v) :
    (1 / (n : ℝ)) * |Real.log (FullSupportWitnessHull.volume D n C)| ≤
      iutInitialThetaSelectedQRootPaperSum D :=
  ordinary_collation_averageAbsLog_le_paperSum_of_global_margin D n C hw hunit hn
    (globalArithmeticMargin_nonneg_of_moduli_low_ramification D he hother)

end
end JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
