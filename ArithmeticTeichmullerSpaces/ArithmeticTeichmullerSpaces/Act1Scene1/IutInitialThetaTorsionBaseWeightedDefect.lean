import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTorsionBaseMassGap

/-!
source-id: JT-SCENE1-INITIAL-THETA-TORSION-BASE-WEIGHTED-DEFECT
source: the actual base-fibre descent identity, strict section-fibre mass gap,
positivity of corrected root logarithms, and Joshi III `eq:weights`.
fidelity: upgrades one strict base-fibre defect to a strict inequality between
the full actual weighted source sum and the corresponding unweighted base
section sum. This is an actual-carrier result and does not identify either
side with the paper L' representative sum or theta volume.
boundary: Scene1/Derived. Original proofs; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue NumberField
open scoped BigOperators
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

private theorem qPilotWeight_le_one_base
    (b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset) :
    Arithmetic.qPilotWeight b.1 ≤ 1 := by
  have h := Arithmetic.qPilotWeight_sum_le_one_of_residueChar_filter
    ({b.1} : Finset (NumberField.FinitePlace D.F))
    (Arithmetic.residueChar b.1) (Arithmetic.residueChar_prime b.1)
  have hf : ({b.1} : Finset (NumberField.FinitePlace D.F)).filter
      (fun z => Arithmetic.residueChar z = Arithmetic.residueChar b.1) = {b.1} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · exact And.left
    · intro hz
      subst z
      exact ⟨rfl, rfl⟩
  rw [hf, Finset.sum_singleton] at h
  exact h

theorem iutInitialThetaTorsionSource_weightedPaperLogSum_lt_baseSectionUnweightedSum :
    (∑ s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset,
      Arithmetic.qPilotWeight s.1 * (-Real.log (actualPaperRootNorm D s))) <
      ∑ b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset,
        -Real.log (actualPaperRootNorm D
          (iutInitialThetaTorsionBaseSection D b)) := by
  rw [iutInitialThetaTorsionSource_weightedPaperLogSum_eq_baseSectionSum D]
  obtain ⟨b₀, hb₀⟩ := iutInitialTheta_exists_baseSection_mass_lt_one D
  have hterm (b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset) :
      0 < -Real.log (actualPaperRootNorm D
        (iutInitialThetaTorsionBaseSection D b)) := by
    apply neg_pos.mpr
    exact Real.log_neg
      (actualPaperRootNorm_mem_Ioo D
        (iutInitialThetaTorsionBaseSection D b)).1
      (actualPaperRootNorm_mem_Ioo D
        (iutInitialThetaTorsionBaseSection D b)).2
  have hcoeff (b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset) :
      Arithmetic.qPilotWeight b.1 /
          (Arithmetic.relRamIdx (iutInitialThetaTorsionBaseSection D b).1 b.1 : ℝ) ≤ 1 := by
    have hrel : (0 : ℝ) < Arithmetic.relRamIdx
        (iutInitialThetaTorsionBaseSection D b).1 b.1 := by
      have hne := Arithmetic.relRamIdx_ne_zero
        ((iutInitialThetaOddSupportTorsionQRootSource D).liesOver
          (iutInitialThetaTorsionBaseSection D b))
      rw [iutInitialThetaTorsionBaseSection_basePlace D b] at hne
      exact_mod_cast Nat.pos_of_ne_zero
        hne
    have hrel1 : (1 : ℝ) ≤ Arithmetic.relRamIdx
        (iutInitialThetaTorsionBaseSection D b).1 b.1 := by
      have hne := Arithmetic.relRamIdx_ne_zero
        ((iutInitialThetaOddSupportTorsionQRootSource D).liesOver
          (iutInitialThetaTorsionBaseSection D b))
      rw [iutInitialThetaTorsionBaseSection_basePlace D b] at hne
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        hne
    exact (div_le_one hrel).mpr
      ((qPilotWeight_le_one_base D b).trans hrel1)
  have hlt (b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset) :
      (Arithmetic.qPilotWeight b.1 /
          (Arithmetic.relRamIdx (iutInitialThetaTorsionBaseSection D b).1 b.1 : ℝ)) *
          (-Real.log (actualPaperRootNorm D
            (iutInitialThetaTorsionBaseSection D b))) ≤
        -Real.log (actualPaperRootNorm D
          (iutInitialThetaTorsionBaseSection D b)) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hcoeff b) (hterm b).le
  have hlt₀ :
      (Arithmetic.qPilotWeight b₀.1 /
          (Arithmetic.relRamIdx (iutInitialThetaTorsionBaseSection D b₀).1 b₀.1 : ℝ)) *
          (-Real.log (actualPaperRootNorm D
            (iutInitialThetaTorsionBaseSection D b₀))) <
        -Real.log (actualPaperRootNorm D
          (iutInitialThetaTorsionBaseSection D b₀)) := by
    simpa only [mul_comm] using mul_lt_of_lt_one_right (hterm b₀) hb₀
  exact Finset.sum_lt_sum (fun b _ => hlt b)
    ⟨b₀, Finset.mem_univ _, hlt₀⟩

end
end JoshiTeich.Act1Scene1
