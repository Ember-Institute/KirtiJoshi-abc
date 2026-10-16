import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOrdinaryLogCorrectionCost

/-!
source-id: JT-SCENE1-ACTUAL-ORDINARY-LOG-COST-ABSORPTION
source: actual base Tate q-order, local degree weights and the explicit
pStar correction cost; Joshi III 3226--3236, 3520--3574, 3624--3631.
fidelity: the local corrected cost is at most the selected paper term iff
d_moduli*(threshold+qOrder) <= d_source*qOrder. These local arithmetic
tests suffice for the full ordinary-log collation bound with no remaining
correction term. The tests are explicit and are not presumed from D.
boundary: Scene1/Derived; no unconditional test, BK/untilt or theta identity.
-/

namespace JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance absorptionPrime (v : iutInitialThetaOddModSupportFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩

def sourceQOrder (v : iutInitialThetaOddModSupportFinset D) : ℕ :=
  (iutInitialThetaOddSupportBaseQPilotSource D).qOrder
    ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace (FullSupportPaperWeightedHull.selected D v))

def sourceThreshold (v : iutInitialThetaOddModSupportFinset D) : ℕ :=
  PrincipalUnitKummer.baseIntegralThreshold D (FullSupportPaperWeightedHull.selected D v)

def arithmeticAbsorption (v : iutInitialThetaOddModSupportFinset D) : Prop :=
  Arithmetic.localDeg v.1 * (sourceThreshold D v + sourceQOrder D v) ≤
    Arithmetic.localDeg (FullSupportPaperWeightedHull.selected D v).1 * sourceQOrder D v

theorem correctedLocalCost_eq_arithmetic (v : iutInitialThetaOddModSupportFinset D) :
    correctedLocalCost D v =
      (Real.log (Arithmetic.residueChar (FullSupportPaperWeightedHull.selected D v).1) /
        ((Arithmetic.inertDeg (FullSupportPaperWeightedHull.selected D v).1 : ℝ) * sourceThreshold D v)) *
          (Arithmetic.localDeg v.1 : ℝ) * (sourceThreshold D v + sourceQOrder D v) := by
  let s := FullSupportPaperWeightedHull.selected D v
  have hf : (Arithmetic.inertDeg s.1 : ℝ) ≠ 0 := by exact_mod_cast (Arithmetic.inertDeg_pos s.1).ne'
  have he : (Arithmetic.ramIdx s.1 : ℝ) ≠ 0 := by exact_mod_cast (Arithmetic.ramIdx_pos s.1).ne'
  have ht : (sourceThreshold D v : ℝ) ≠ 0 := by
    exact_mod_cast (PrincipalUnitKummer.baseIntegralThreshold_pos D s).ne'
  unfold correctedLocalCost selectedPaperTerm localCorrectionCost
  rw [FullSupportPaperWeightedHull.weight_eq_localDeg_ratio,
    actualPaperRootNorm_negLog_eq_paperTerm, PrincipalUnitKummer.qroot_ordp_eq_baseQOrder]
  change (Arithmetic.localDeg v.1 : ℝ) / Arithmetic.localDeg s.1 *
      ((Arithmetic.ramIdx s.1 : ℝ) * ((sourceQOrder D v : ℝ) / sourceThreshold D v) *
        Real.log (Arithmetic.residueChar s.1)) +
      (Arithmetic.localDeg v.1 : ℝ) / Arithmetic.inertDeg s.1 * Real.log (Arithmetic.residueChar s.1) = _
  dsimp only [s] at hf he ⊢
  simp only [Arithmetic.localDeg, Nat.cast_mul]
  field_simp [hf, he, ht]
  <;> ring

theorem selectedPaperTerm_eq_arithmetic (v : iutInitialThetaOddModSupportFinset D) :
    selectedPaperTerm D v =
      (Real.log (Arithmetic.residueChar (FullSupportPaperWeightedHull.selected D v).1) /
        ((Arithmetic.inertDeg (FullSupportPaperWeightedHull.selected D v).1 : ℝ) * sourceThreshold D v)) *
          (Arithmetic.localDeg (FullSupportPaperWeightedHull.selected D v).1 : ℝ) * sourceQOrder D v := by
  let s := FullSupportPaperWeightedHull.selected D v
  have hf : (Arithmetic.inertDeg s.1 : ℝ) ≠ 0 := by exact_mod_cast (Arithmetic.inertDeg_pos s.1).ne'
  have ht : (sourceThreshold D v : ℝ) ≠ 0 := by
    exact_mod_cast (PrincipalUnitKummer.baseIntegralThreshold_pos D s).ne'
  rw [selectedPaperTerm, actualPaperRootNorm_negLog_eq_paperTerm, PrincipalUnitKummer.qroot_ordp_eq_baseQOrder]
  change (Arithmetic.ramIdx s.1 : ℝ) * ((sourceQOrder D v : ℝ) / sourceThreshold D v) *
    Real.log (Arithmetic.residueChar s.1) = _
  dsimp only [s] at hf ⊢
  simp only [Arithmetic.localDeg, Nat.cast_mul]
  field_simp [hf, ht]
  <;> ring

theorem correctedLocalCost_le_paperTerm_iff_arithmetic (v : iutInitialThetaOddModSupportFinset D) :
    correctedLocalCost D v ≤ selectedPaperTerm D v ↔ arithmeticAbsorption D v := by
  have hp : 0 < Real.log (Arithmetic.residueChar (FullSupportPaperWeightedHull.selected D v).1) :=
    Real.log_pos (by exact_mod_cast (Arithmetic.residueChar_prime _).one_lt)
  have hf : (0 : ℝ) < Arithmetic.inertDeg (FullSupportPaperWeightedHull.selected D v).1 :=
    by exact_mod_cast Arithmetic.inertDeg_pos _
  have ht : (0 : ℝ) < sourceThreshold D v :=
    by exact_mod_cast PrincipalUnitKummer.baseIntegralThreshold_pos D (FullSupportPaperWeightedHull.selected D v)
  rw [correctedLocalCost_eq_arithmetic, selectedPaperTerm_eq_arithmetic, mul_assoc, mul_assoc,
    mul_le_mul_iff_right₀ (div_pos hp (mul_pos hf ht))]
  exact_mod_cast (Iff.rfl : arithmeticAbsorption D v ↔ arithmeticAbsorption D v)

theorem correctedCost_le_selectedPaperSum_of_arithmetic
    (h : ∀ v, arithmeticAbsorption D v) :
    FullSupportPaperWeightedHull.weightedPaperSum D - Real.log (correction D 1) ≤
      iutInitialThetaSelectedQRootPaperSum D := by
  rw [correctedCost_eq_sum, selectedPaperSum_eq_sum_terms]
  exact Finset.sum_le_sum (fun v _ => (correctedLocalCost_le_paperTerm_iff_arithmetic D v).mpr (h v))

theorem arithmeticAbsorption_of_small_and_degree_gap
    (v : iutInitialThetaOddModSupportFinset D)
    (hq : sourceThreshold D v ≤ sourceQOrder D v)
    (hd : 2 * Arithmetic.localDeg v.1 ≤ Arithmetic.localDeg (FullSupportPaperWeightedHull.selected D v).1) :
    arithmeticAbsorption D v := by
  unfold arithmeticAbsorption
  calc
    _ ≤ Arithmetic.localDeg v.1 * (sourceQOrder D v + sourceQOrder D v) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_right hq _)
    _ = (2 * Arithmetic.localDeg v.1) * sourceQOrder D v := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hd

variable (n : ℕ) {κ : Type*}
variable (C : ∀ v : iutInitialThetaOddModSupportFinset D, κ → Set (packet D n v).Tensor)
variable (hw : ∀ v, witness D n v ∈ ⋃ k, C v k)
variable (hunit : ∀ v k, C v k ⊆ (packet D n v).normalization)

include hw hunit in
theorem ordinary_collation_averageAbsLog_le_selectedPaperSum
    (hn : 0 < n) (h : ∀ v, arithmeticAbsorption D v) :
    (1 / (n : ℝ)) * |Real.log (FullSupportWitnessHull.volume D n C)| ≤
      iutInitialThetaSelectedQRootPaperSum D :=
  (ordinary_collation_averageAbsLog_le_correctedCost D n C hw hunit hn).trans
    (correctedCost_le_selectedPaperSum_of_arithmetic D h)

end
end JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
