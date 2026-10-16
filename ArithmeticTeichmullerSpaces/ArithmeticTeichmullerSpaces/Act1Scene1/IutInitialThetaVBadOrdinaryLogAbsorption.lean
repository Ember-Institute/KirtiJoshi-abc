import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOrdinaryLogCostAbsorption
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRepresentativeRamificationGap

/-!
source-id: JT-SCENE1-ACTUAL-VBAD-ORDINARY-LOG-ABSORPTION
source: actual q-root ramification, VBad q-order coprimality and local
degree towers; Joshi III initial theta data and 3520--3574, 3624--3631.
fidelity: actual VBad forces source local degree at least ell times the
moduli degree. Thus threshold <= (ell-1)*baseQOrder suffices to absorb the
ordinary-log correction there. The degree lower bound is derived; the
remaining numerical condition and complementary places stay explicit.
boundary: Scene1/Derived; no BK/untilt or paper thetaVolume identity.
-/

namespace JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance vbadAbsorptionPrime (v : iutInitialThetaOddModSupportFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩

theorem vbad_source_localDeg_ge_ell_mul
    (v : iutInitialThetaOddModSupportFinset D) (hv : v.1 ∈ D.VBad) :
    D.prime.ℓ * Arithmetic.localDeg v.1 ≤
      Arithmetic.localDeg (FullSupportPaperWeightedHull.selected D v).1 := by
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let s := FullSupportPaperWeightedHull.selected D v
  let b := R.basePlace s
  have hb : b.1 = iutInitialThetaSectionBasePlace D v.1 :=
    iutInitialThetaOddSupportSelectedQRootPlace_basePlace_eq_sectionBasePlace D v.1
      ((iutInitialThetaOddModSupport_finite D).mem_toFinset.mp v.2)
  have hbv : Ideal.LiesOver b.1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal := by
    rw [hb]
    exact iutInitialThetaSectionBasePlace_liesOver D v.1
  have hw : b.1 ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad := ⟨v.1, hv, hbv⟩
  have hdiv := iutInitialThetaEll_dvd_qRootRelativeRamIdx_on_vbad D s hw
  have hell : D.prime.ℓ ≤ Arithmetic.relRamIdx s.1 b.1 :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Arithmetic.relRamIdx_ne_zero (R.liesOver s))) hdiv
  have hsb := Arithmetic.localDeg_eq_mul (R.liesOver s)
  have hfb : 0 < Arithmetic.relInertDeg s.1 b.1 := by
    have hp : 0 < Arithmetic.relRamIdx s.1 b.1 * Arithmetic.relInertDeg s.1 b.1 :=
      Nat.pos_of_mul_pos_left (hsb ▸ Arithmetic.localDeg_pos s.1)
    exact Nat.pos_of_mul_pos_left hp
  change 1 ≤ Arithmetic.relInertDeg s.1 b.1 at hfb
  have hbdeg : Arithmetic.localDeg v.1 ≤ Arithmetic.localDeg b.1 := by
    have hbvdeg := Arithmetic.localDeg_eq_mul hbv
    have hp : 0 < Arithmetic.relRamIdx b.1 v.1 * Arithmetic.relInertDeg b.1 v.1 :=
      Nat.pos_of_mul_pos_left (hbvdeg ▸ Arithmetic.localDeg_pos b.1)
    calc
      _ = Arithmetic.localDeg v.1 * 1 := (mul_one _).symm
      _ ≤ _ := (Nat.mul_le_mul_left _ hp).trans_eq hbvdeg.symm
  calc
    D.prime.ℓ * Arithmetic.localDeg v.1 ≤ Arithmetic.relRamIdx s.1 b.1 * Arithmetic.localDeg b.1 :=
      Nat.mul_le_mul hell hbdeg
    _ = Arithmetic.localDeg b.1 * Arithmetic.relRamIdx s.1 b.1 := mul_comm _ _
    _ ≤ Arithmetic.localDeg b.1 * (Arithmetic.relRamIdx s.1 b.1 * Arithmetic.relInertDeg s.1 b.1) :=
      Nat.mul_le_mul_left _ (by simpa only [mul_one] using Nat.mul_le_mul_left (Arithmetic.relRamIdx s.1 b.1) hfb)
    _ = _ := hsb.symm

theorem vbad_source_localDeg_ge_two_mul
    (v : iutInitialThetaOddModSupportFinset D) (hv : v.1 ∈ D.VBad) :
    2 * Arithmetic.localDeg v.1 ≤ Arithmetic.localDeg (FullSupportPaperWeightedHull.selected D v).1 :=
  (Nat.mul_le_mul_right _ (le_trans (by decide : 2 ≤ 5) D.prime.five_le)).trans
    (vbad_source_localDeg_ge_ell_mul D v hv)

theorem arithmeticAbsorption_on_vbad_of_relaxed_order
    (v : iutInitialThetaOddModSupportFinset D) (hv : v.1 ∈ D.VBad)
    (hq : sourceThreshold D v ≤ (D.prime.ℓ - 1) * sourceQOrder D v) :
    arithmeticAbsorption D v := by
  have hell : 1 ≤ D.prime.ℓ := le_trans (by decide : 1 ≤ 5) D.prime.five_le
  have hsum : sourceThreshold D v + sourceQOrder D v ≤ D.prime.ℓ * sourceQOrder D v := by
    calc
      _ ≤ (D.prime.ℓ - 1) * sourceQOrder D v + sourceQOrder D v := Nat.add_le_add_right hq _
      _ = ((D.prime.ℓ - 1) + 1) * sourceQOrder D v := by ring
      _ = _ := by rw [Nat.sub_add_cancel hell]
  unfold arithmeticAbsorption
  calc
    _ ≤ Arithmetic.localDeg v.1 * (D.prime.ℓ * sourceQOrder D v) := Nat.mul_le_mul_left _ hsum
    _ = (D.prime.ℓ * Arithmetic.localDeg v.1) * sourceQOrder D v := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (vbad_source_localDeg_ge_ell_mul D v hv)

theorem arithmeticAbsorption_on_vbad_of_small
    (v : iutInitialThetaOddModSupportFinset D) (hv : v.1 ∈ D.VBad)
    (hq : sourceThreshold D v ≤ sourceQOrder D v) : arithmeticAbsorption D v :=
  arithmeticAbsorption_of_small_and_degree_gap D v hq (vbad_source_localDeg_ge_two_mul D v hv)

theorem correctedLocalCost_le_paperTerm_on_vbad
    (v : iutInitialThetaOddModSupportFinset D) (hv : v.1 ∈ D.VBad)
    (hq : sourceThreshold D v ≤ (D.prime.ℓ - 1) * sourceQOrder D v) :
    correctedLocalCost D v ≤ selectedPaperTerm D v :=
  (correctedLocalCost_le_paperTerm_iff_arithmetic D v).mpr
    (arithmeticAbsorption_on_vbad_of_relaxed_order D v hv hq)

theorem correctedCost_le_selectedPaperSum_of_vbad_and_complement
    (hq : ∀ v : iutInitialThetaOddModSupportFinset D, v.1 ∈ D.VBad →
      sourceThreshold D v ≤ (D.prime.ℓ - 1) * sourceQOrder D v)
    (hother : ∀ v : iutInitialThetaOddModSupportFinset D, v.1 ∉ D.VBad → arithmeticAbsorption D v) :
    FullSupportPaperWeightedHull.weightedPaperSum D - Real.log (correction D 1) ≤
      iutInitialThetaSelectedQRootPaperSum D := by
  apply correctedCost_le_selectedPaperSum_of_arithmetic D
  intro v
  by_cases hv : v.1 ∈ D.VBad
  · exact arithmeticAbsorption_on_vbad_of_relaxed_order D v hv (hq v hv)
  · exact hother v hv

variable (n : ℕ) {κ : Type*}
variable (C : ∀ v : iutInitialThetaOddModSupportFinset D, κ → Set (packet D n v).Tensor)
variable (hw : ∀ v, witness D n v ∈ ⋃ k, C v k)
variable (hunit : ∀ v k, C v k ⊆ (packet D n v).normalization)

include hw hunit in
theorem ordinary_collation_averageAbsLog_le_selectedPaperSum_of_vbad
    (hn : 0 < n)
    (hq : ∀ v : iutInitialThetaOddModSupportFinset D, v.1 ∈ D.VBad →
      sourceThreshold D v ≤ (D.prime.ℓ - 1) * sourceQOrder D v)
    (hother : ∀ v : iutInitialThetaOddModSupportFinset D, v.1 ∉ D.VBad → arithmeticAbsorption D v) :
    (1 / (n : ℝ)) * |Real.log (FullSupportWitnessHull.volume D n C)| ≤
      iutInitialThetaSelectedQRootPaperSum D :=
  (ordinary_collation_averageAbsLog_le_correctedCost D n C hw hunit hn).trans
    (correctedCost_le_selectedPaperSum_of_vbad_and_complement D hq hother)

end
end JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
