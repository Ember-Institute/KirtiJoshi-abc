import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOrdinaryLogCostAbsorption

/-!
source-id: JT-SCENE1-ACTUAL-ORDINARY-LOG-GLOBAL-MARGIN
source: actual base Tate q-orders, local degrees and correction-cost sums;
Joshi III 3520--3574, 3624--3631.
fidelity: computes the total signed arithmetic margin on the original full
moduli carrier. Nonnegative total margin is equivalent to absorption of
the full correction cost, allowing compensation between different places.
boundary: Scene1/Derived; no actual margin sign or paper theta identity.
-/

namespace JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance globalMarginPrime (v : iutInitialThetaOddModSupportFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩

/-- The subtraction is in R, so a failing place contributes its signed deficit. -/
def localArithmeticMargin (v : iutInitialThetaOddModSupportFinset D) : ℝ :=
  (Real.log (Arithmetic.residueChar (FullSupportPaperWeightedHull.selected D v).1) /
    ((Arithmetic.inertDeg (FullSupportPaperWeightedHull.selected D v).1 : ℝ) * sourceThreshold D v)) *
      ((Arithmetic.localDeg (FullSupportPaperWeightedHull.selected D v).1 : ℝ) * sourceQOrder D v -
        (Arithmetic.localDeg v.1 : ℝ) * (sourceThreshold D v + sourceQOrder D v))

theorem localArithmeticMargin_eq_difference (v : iutInitialThetaOddModSupportFinset D) :
    localArithmeticMargin D v = selectedPaperTerm D v - correctedLocalCost D v := by
  rw [correctedLocalCost_eq_arithmetic, selectedPaperTerm_eq_arithmetic]
  unfold localArithmeticMargin
  ring

theorem localArithmeticMargin_nonneg_iff (v : iutInitialThetaOddModSupportFinset D) :
    0 ≤ localArithmeticMargin D v ↔ arithmeticAbsorption D v := by
  rw [localArithmeticMargin_eq_difference, sub_nonneg,
    correctedLocalCost_le_paperTerm_iff_arithmetic]

def globalArithmeticMargin : ℝ :=
  ∑ v : iutInitialThetaOddModSupportFinset D, localArithmeticMargin D v

theorem globalArithmeticMargin_eq_difference :
    globalArithmeticMargin D = iutInitialThetaSelectedQRootPaperSum D -
      (FullSupportPaperWeightedHull.weightedPaperSum D - Real.log (correction D 1)) := by
  rw [globalArithmeticMargin, selectedPaperSum_eq_sum_terms, correctedCost_eq_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun v _ => localArithmeticMargin_eq_difference D v)

theorem globalArithmeticMargin_nonneg_iff :
    0 ≤ globalArithmeticMargin D ↔
      FullSupportPaperWeightedHull.weightedPaperSum D - Real.log (correction D 1) ≤
        iutInitialThetaSelectedQRootPaperSum D := by
  rw [globalArithmeticMargin_eq_difference, sub_nonneg]

theorem globalArithmeticMargin_nonneg_of_local_tests (h : ∀ v, arithmeticAbsorption D v) :
    0 ≤ globalArithmeticMargin D :=
  Finset.sum_nonneg (fun v _ => (localArithmeticMargin_nonneg_iff D v).mpr (h v))

variable (n : ℕ) {κ : Type*}
variable (C : ∀ v : iutInitialThetaOddModSupportFinset D, κ → Set (packet D n v).Tensor)
variable (hw : ∀ v, witness D n v ∈ ⋃ k, C v k)
variable (hunit : ∀ v k, C v k ⊆ (packet D n v).normalization)

include hw hunit in
theorem ordinary_collation_averageAbsLog_le_paperSum_of_global_margin
    (hn : 0 < n) (h : 0 ≤ globalArithmeticMargin D) :
    (1 / (n : ℝ)) * |Real.log (FullSupportWitnessHull.volume D n C)| ≤
      iutInitialThetaSelectedQRootPaperSum D :=
  (ordinary_collation_averageAbsLog_le_correctedCost D n C hw hunit hn).trans
    ((globalArithmeticMargin_nonneg_iff D).mp h)

end
end JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
