import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRelativeQRootChoice
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalQRootNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
source-id: JT-SCENE1-INITIAL-THETA-PAPER-RELATIVE-NORM-BRIDGE
source: Joshi III paper root correction (`1/f_s`) and actual relative
completion degree (`[K_s:K_v]⁻¹`), with the ramification/inertia tower.
fidelity: proves the exact local conversion between the paper-corrected root
norm and the actual relative-degree weighted raw root factor. It does not
identify either value with a paper `L'` carrier, a Bloch--Kato class, or a hull.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open JoshiTeich.Prologue.Arithmetic
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

def actualPaperRootNorm
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) : ℝ :=
  ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot s‖ ^
    (1 / (inertDeg s.1 : ℝ))

theorem actualPaperRootNorm_mem_Ioo
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    actualPaperRootNorm D s ∈ Set.Ioo (0 : ℝ) 1 := by
  unfold actualPaperRootNorm
  have hn : 0 < ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot s‖ :=
    norm_pos_iff.mpr ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero s)
  have hf : (0 : ℝ) < inertDeg s.1 := by exact_mod_cast inertDeg_pos s.1
  exact ⟨Real.rpow_pos_of_pos hn _,
    Real.rpow_lt_one hn.le (iutInitialThetaFullQRoot_norm_lt_one D s) (one_div_pos.mpr hf)⟩

theorem relativeFactor_eq_paperRootNorm_rpow
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hsv : Ideal.LiesOver s.1.maximalIdeal.asIdeal v.maximalIdeal.asIdeal) :
    iutInitialThetaRelativeQRootFactorAt D v s =
      actualPaperRootNorm D s ^ ((localDeg v : ℝ) / ramIdx s.1) := by
  unfold iutInitialThetaRelativeQRootFactorAt actualPaperRootNorm
  rw [← Real.rpow_mul (norm_nonneg _)]
  have hs : (inertDeg s.1 : ℝ) ≠ 0 := by exact_mod_cast (inertDeg_pos s.1).ne'
  have he : (ramIdx s.1 : ℝ) ≠ 0 := by exact_mod_cast (ramIdx_pos s.1).ne'
  have hlocal : (localDeg s.1 : ℝ) = (ramIdx s.1 : ℝ) * inertDeg s.1 := by
    unfold localDeg
    push_cast
    ring
  rw [hlocal]
  field_simp [hs, he]

theorem relativeFactor_negLog_eq_paperRootNorm_negLog_mul_degree_ratio
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hsv : Ideal.LiesOver s.1.maximalIdeal.asIdeal v.maximalIdeal.asIdeal) :
    -Real.log (iutInitialThetaRelativeQRootFactorAt D v s) =
      ((localDeg v : ℝ) / ramIdx s.1) * (-Real.log (actualPaperRootNorm D s)) := by
  rw [relativeFactor_eq_paperRootNorm_rpow D v s hsv,
    Real.log_rpow (actualPaperRootNorm_mem_Ioo D s).1]
  ring

end
end JoshiTeich.Act1Scene1
