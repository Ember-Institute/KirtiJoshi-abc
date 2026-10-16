import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOrdinaryLogCompensationBudget
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadSelectedSupportDefect

/-!
source-id: JT-SCENE1-ACTUAL-CORRECTION-COST-COVERAGE
source: actual positive correction costs, nonempty VBad and the existing
full-support coverage criterion; Joshi III 1028--1055, 3520--3574, 3624--3631.
fidelity: zero complementary correction cost is equivalent to full VBad
coverage, and to the old omitted paper sum vanishing. Coverage and the
moduli ramification bound give a strictly positive global margin and a
strict ordinary-log collation bound, without a separate cost budget.
boundary: Scene1/Derived; coverage is not inferred from inclusion alone.
-/

namespace JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance coverageCostPrime (v : iutInitialThetaOddModSupportFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩

theorem vbadCorrectionCost_pos : 0 < vbadCorrectionCost D := by
  obtain ⟨v, hv⟩ := D.global.bad_nonempty
  have hfull : v ∈ iutInitialThetaOddModSupportFinset D :=
    (iutInitialThetaOddModSupport_finite D).mem_toFinset.mpr
      (iutInitialThetaVBad_subset_VBadOdd D hv)
  let w : iutInitialThetaOddModSupportFinset D := ⟨v, hfull⟩
  have hle := Finset.single_le_sum (s := Finset.univ)
    (f := fun z : iutInitialThetaOddModSupportFinset D =>
      if z.1 ∈ D.VBad then localCorrectionCost D z else 0)
    (fun z _ => by split_ifs <;> simp_all [(localCorrectionCost_pos D z).le])
    (Finset.mem_univ w)
  change (if w.1 ∈ D.VBad then localCorrectionCost D w else 0) ≤ vbadCorrectionCost D at hle
  rw [if_pos hv] at hle
  exact (localCorrectionCost_pos D w).trans_le hle

theorem complementCorrectionCost_eq_zero_iff_all_mem_vbad :
    complementCorrectionCost D = 0 ↔ ∀ v : iutInitialThetaOddModSupportFinset D, v.1 ∈ D.VBad := by
  constructor
  · intro hz v
    by_contra hv
    have hle := Finset.single_le_sum (s := Finset.univ)
      (f := fun z : iutInitialThetaOddModSupportFinset D =>
        if z.1 ∈ D.VBad then 0 else localCorrectionCost D z)
      (fun z _ => by split_ifs <;> simp_all [(localCorrectionCost_pos D z).le])
      (Finset.mem_univ v)
    change (if v.1 ∈ D.VBad then 0 else localCorrectionCost D v) ≤ complementCorrectionCost D at hle
    rw [if_neg hv, hz] at hle
    exact (not_le_of_gt (localCorrectionCost_pos D v)) hle
  · intro h
    unfold complementCorrectionCost
    exact Finset.sum_eq_zero (fun v _ => if_pos (h v))

theorem complementCorrectionCost_eq_zero_iff_coverage :
    complementCorrectionCost D = 0 ↔
      iutInitialThetaVBadModuliFinset D = iutInitialThetaOddModSupportFinset D := by
  rw [complementCorrectionCost_eq_zero_iff_all_mem_vbad]
  constructor
  · intro h
    apply Finset.Subset.antisymm (Finset.filter_subset _ _)
    intro v hv
    exact (mem_iutInitialThetaVBadModuliFinset_iff D v).mpr (h ⟨v, hv⟩)
  · intro h v
    exact (mem_iutInitialThetaVBadModuliFinset_iff D v.1).mp (h.symm ▸ v.2)

theorem complementCorrectionCost_eq_zero_iff_omittedPaperSum_eq_zero :
    complementCorrectionCost D = 0 ↔ VBadSelectedPaper.omittedPaperSum D = 0 :=
  (complementCorrectionCost_eq_zero_iff_coverage D).trans
    (VBadSelectedPaper.omittedPaperSum_eq_zero_iff_coverage D).symm

theorem globalArithmeticMargin_pos_of_full_coverage
    (hcover : iutInitialThetaVBadModuliFinset D = iutInitialThetaOddModSupportFinset D)
    (he : ∀ v : iutInitialThetaOddModSupportFinset D, v.1 ∈ D.VBad → Arithmetic.ramIdx v.1 ≤ 2) :
    0 < globalArithmeticMargin D := by
  have hz := (complementCorrectionCost_eq_zero_iff_coverage D).mpr hcover
  have h := five_mul_globalMargin_ge_cost_budget D he
  rw [hz, mul_zero, sub_zero] at h
  have hp := vbadCorrectionCost_pos D
  linarith

theorem correctedCost_lt_selectedPaperSum_of_full_coverage
    (hcover : iutInitialThetaVBadModuliFinset D = iutInitialThetaOddModSupportFinset D)
    (he : ∀ v : iutInitialThetaOddModSupportFinset D, v.1 ∈ D.VBad → Arithmetic.ramIdx v.1 ≤ 2) :
    FullSupportPaperWeightedHull.weightedPaperSum D - Real.log (correction D 1) <
      iutInitialThetaSelectedQRootPaperSum D := by
  have h := globalArithmeticMargin_pos_of_full_coverage D hcover he
  rw [globalArithmeticMargin_eq_difference] at h
  linarith

variable (n : ℕ) {κ : Type*}
variable (C : ∀ v : iutInitialThetaOddModSupportFinset D, κ → Set (packet D n v).Tensor)
variable (hw : ∀ v, witness D n v ∈ ⋃ k, C v k)
variable (hunit : ∀ v k, C v k ⊆ (packet D n v).normalization)

include hw hunit in
theorem ordinary_collation_averageAbsLog_lt_selectedPaperSum_of_full_coverage
    (hn : 0 < n)
    (hcover : iutInitialThetaVBadModuliFinset D = iutInitialThetaOddModSupportFinset D)
    (he : ∀ v : iutInitialThetaOddModSupportFinset D, v.1 ∈ D.VBad → Arithmetic.ramIdx v.1 ≤ 2) :
    (1 / (n : ℝ)) * |Real.log (FullSupportWitnessHull.volume D n C)| <
      iutInitialThetaSelectedQRootPaperSum D :=
  (ordinary_collation_averageAbsLog_le_correctedCost D n C hw hunit hn).trans_lt
    (correctedCost_lt_selectedPaperSum_of_full_coverage D hcover he)

end
end JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
