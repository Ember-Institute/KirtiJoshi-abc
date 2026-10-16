import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOrdinaryLogMarginDeficit
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaModuliRamificationAbsorption

/-!
source-id: JT-SCENE1-ACTUAL-ORDINARY-LOG-COMPENSATION-BUDGET
source: actual base q-order >=6, VBad local degree tower and local
correction costs; Joshi III 3520--3574, 3624--3631.
fidelity: VBad margins are at least one fifth of the local correction
cost when the moduli ramification index is at most two. All other local
deficits are bounded by their correction costs. A comparison of the two
cost sums therefore suffices for the full margin and collation bound,
without local absorption tests on the complement. This cost comparison
and the moduli ramification condition remain explicit.
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
local instance compensationPrime (v : iutInitialThetaOddModSupportFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩

theorem localArithmeticMargin_ge_fifth_correctionCost_on_vbad
    (v : iutInitialThetaOddModSupportFinset D) (hv : v.1 ∈ D.VBad)
    (he : Arithmetic.ramIdx v.1 ≤ 2) :
    localCorrectionCost D v / 5 ≤ localArithmeticMargin D v := by
  let s := FullSupportPaperWeightedHull.selected D v
  let b := (iutInitialThetaOddSupportTorsionQRootSource D).basePlace s
  have hb : b.1 = iutInitialThetaSectionBasePlace D v.1 :=
    iutInitialThetaOddSupportSelectedQRootPlace_basePlace_eq_sectionBasePlace D v.1
      ((iutInitialThetaOddModSupport_finite D).mem_toFinset.mp v.2)
  have hbv : Ideal.LiesOver b.1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal := by
    rw [hb]
    exact iutInitialThetaSectionBasePlace_liesOver D v.1
  let t := D.prime.ℓ * Arithmetic.relRamIdx b.1 v.1
  have hr : 1 ≤ Arithmetic.relRamIdx b.1 v.1 :=
    Nat.one_le_iff_ne_zero.mpr (Arithmetic.relRamIdx_ne_zero hbv)
  have ht : 5 ≤ t := D.prime.five_le.trans (by
    simpa only [mul_one] using Nat.mul_le_mul_left D.prime.ℓ hr)
  have hT : sourceThreshold D v = 2 * Arithmetic.ramIdx v.1 * t := by
    change 2 * D.prime.ℓ * Arithmetic.ramIdx b.1 = _
    rw [Arithmetic.ramIdx_eq_mul hbv]
    dsimp only [t]
    ring
  have hT4 : sourceThreshold D v ≤ 4 * t := by
    rw [hT]
    simpa using Nat.mul_le_mul_right t (Nat.mul_le_mul_left 2 he)
  have hq : 6 ≤ sourceQOrder D v := baseTateParameter_qOrder_ge_six D _
  have hnum : 6 * sourceThreshold D v + 5 * sourceQOrder D v ≤ 5 * t * sourceQOrder D v := by
    calc
      _ ≤ 24 * t + 5 * sourceQOrder D v := by omega
      _ ≤ (5 * t - 5) * 6 + 5 * sourceQOrder D v := by omega
      _ ≤ (5 * t - 5) * sourceQOrder D v + 5 * sourceQOrder D v :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hq) _
      _ = _ := by rw [← add_mul, Nat.sub_add_cancel (show 5 ≤ 5 * t by omega)]
  have hd := vbad_source_localDeg_ge_ell_mul_baseRelativeRamIdx D v hv
  have hnat : Arithmetic.localDeg v.1 * (6 * sourceThreshold D v + 5 * sourceQOrder D v) ≤
      5 * Arithmetic.localDeg s.1 * sourceQOrder D v := by
    calc
      _ ≤ Arithmetic.localDeg v.1 * (5 * t * sourceQOrder D v) := Nat.mul_le_mul_left _ hnum
      _ = (t * Arithmetic.localDeg v.1) * (5 * sourceQOrder D v) := by ring
      _ ≤ Arithmetic.localDeg s.1 * (5 * sourceQOrder D v) := Nat.mul_le_mul_right _ hd
      _ = _ := by ring
  have hreal : (Arithmetic.localDeg v.1 : ℝ) * (6 * sourceThreshold D v + 5 * sourceQOrder D v) ≤
      5 * Arithmetic.localDeg s.1 * sourceQOrder D v := by exact_mod_cast hnat
  let A := Real.log (Arithmetic.residueChar s.1) /
    ((Arithmetic.inertDeg s.1 : ℝ) * sourceThreshold D v)
  have hA : 0 ≤ A := div_nonneg
    (Real.log_nonneg (by exact_mod_cast (Arithmetic.residueChar_prime s.1).one_le))
    (mul_nonneg (by positivity) (by positivity))
  have hcost : localCorrectionCost D v = A * Arithmetic.localDeg v.1 * sourceThreshold D v := by
    have hf : (Arithmetic.inertDeg s.1 : ℝ) ≠ 0 := by exact_mod_cast (Arithmetic.inertDeg_pos s.1).ne'
    have hT0 : (sourceThreshold D v : ℝ) ≠ 0 := by
      exact_mod_cast (PrincipalUnitKummer.baseIntegralThreshold_pos D s).ne'
    unfold localCorrectionCost
    dsimp only [A, s] at hf ⊢
    field_simp [hf, hT0]
    <;> ring
  rw [hcost]
  change (A * Arithmetic.localDeg v.1 * sourceThreshold D v) / 5 ≤
    A * ((Arithmetic.localDeg s.1 : ℝ) * sourceQOrder D v -
      (Arithmetic.localDeg v.1 : ℝ) * (sourceThreshold D v + sourceQOrder D v))
  have hbracket : (Arithmetic.localDeg v.1 : ℝ) * sourceThreshold D v ≤
      5 * ((Arithmetic.localDeg s.1 : ℝ) * sourceQOrder D v -
        (Arithmetic.localDeg v.1 : ℝ) * (sourceThreshold D v + sourceQOrder D v)) := by nlinarith
  have hscale := mul_le_mul_of_nonneg_left hbracket hA
  nlinarith

def vbadCorrectionCost : ℝ :=
  ∑ v : iutInitialThetaOddModSupportFinset D, if v.1 ∈ D.VBad then localCorrectionCost D v else 0

def complementCorrectionCost : ℝ :=
  ∑ v : iutInitialThetaOddModSupportFinset D, if v.1 ∈ D.VBad then 0 else localCorrectionCost D v

theorem five_mul_globalMargin_ge_cost_budget
    (he : ∀ v : iutInitialThetaOddModSupportFinset D, v.1 ∈ D.VBad → Arithmetic.ramIdx v.1 ≤ 2) :
    vbadCorrectionCost D - 5 * complementCorrectionCost D ≤ 5 * globalArithmeticMargin D := by
  have hlocal (v : iutInitialThetaOddModSupportFinset D) :
      (if v.1 ∈ D.VBad then localCorrectionCost D v else 0) -
        5 * (if v.1 ∈ D.VBad then 0 else localCorrectionCost D v) ≤ 5 * localArithmeticMargin D v := by
    by_cases hv : v.1 ∈ D.VBad
    · simp only [if_pos hv, mul_zero, sub_zero]
      linarith [localArithmeticMargin_ge_fifth_correctionCost_on_vbad D v hv (he v hv)]
    · simp only [if_neg hv]
      linarith [localArithmeticMargin_ge_neg_correctionCost D v]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hlocal v)
  simpa only [vbadCorrectionCost, complementCorrectionCost, globalArithmeticMargin,
    Finset.sum_sub_distrib, ← Finset.mul_sum] using hsum

theorem globalArithmeticMargin_nonneg_of_cost_budget
    (he : ∀ v : iutInitialThetaOddModSupportFinset D, v.1 ∈ D.VBad → Arithmetic.ramIdx v.1 ≤ 2)
    (hbudget : 5 * complementCorrectionCost D ≤ vbadCorrectionCost D) :
    0 ≤ globalArithmeticMargin D := by
  have h := five_mul_globalMargin_ge_cost_budget D he
  linarith

theorem correctedCost_le_selectedPaperSum_of_cost_budget
    (he : ∀ v : iutInitialThetaOddModSupportFinset D, v.1 ∈ D.VBad → Arithmetic.ramIdx v.1 ≤ 2)
    (hbudget : 5 * complementCorrectionCost D ≤ vbadCorrectionCost D) :
    FullSupportPaperWeightedHull.weightedPaperSum D - Real.log (correction D 1) ≤
      iutInitialThetaSelectedQRootPaperSum D :=
  (globalArithmeticMargin_nonneg_iff D).mp (globalArithmeticMargin_nonneg_of_cost_budget D he hbudget)

variable (n : ℕ) {κ : Type*}
variable (C : ∀ v : iutInitialThetaOddModSupportFinset D, κ → Set (packet D n v).Tensor)
variable (hw : ∀ v, witness D n v ∈ ⋃ k, C v k)
variable (hunit : ∀ v k, C v k ⊆ (packet D n v).normalization)

include hw hunit in
theorem ordinary_collation_averageAbsLog_le_selectedPaperSum_of_cost_budget
    (hn : 0 < n)
    (he : ∀ v : iutInitialThetaOddModSupportFinset D, v.1 ∈ D.VBad → Arithmetic.ramIdx v.1 ≤ 2)
    (hbudget : 5 * complementCorrectionCost D ≤ vbadCorrectionCost D) :
    (1 / (n : ℝ)) * |Real.log (FullSupportWitnessHull.volume D n C)| ≤
      iutInitialThetaSelectedQRootPaperSum D :=
  ordinary_collation_averageAbsLog_le_paperSum_of_global_margin D n C hw hunit hn
    (globalArithmeticMargin_nonneg_of_cost_budget D he hbudget)

end
end JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
