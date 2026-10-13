import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRelativeQRootFactor
import Mathlib.Tactic.Linarith

/-!
source-id: JT-SCENE1-INITIAL-THETA-RELATIVE-QROOT-CHOICE
source: actual root power equation, Tate j-norm identity, completion norm
transfer and actual relative degrees; Joshi III eq:weights.
fidelity: proves the relative-weighted raw root factor is independent of the
actual torsion place chosen over one moduli place in a fixed InitialThetaData.
The value is determined by its moduli j-log and ell. Paper carrier, untilt,
norm and tensor-region presentation identifications remain separate obligations.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

theorem iutInitialThetaFullQRoot_pow_norm_inv_eq_torsionJNorm
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    (‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot s‖ ^ (2 * D.prime.ℓ))⁻¹ =
      ‖NumberField.FinitePlace.embedding s.1.maximalIdeal
        (algebraMap D.F ↥D.prime.torsionField D.E.j)‖ := by
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let b := R.basePlace s
  let t := iutInitialThetaOddSupportBaseTateParameterAtCurvePlace D b.1 (B.mem_badPlaces b)
  have hq : (t.q : b.1.maximalIdeal.adicCompletion D.F) = B.tateParameter b := rfl
  have hj : ‖NumberField.FinitePlace.embedding b.1.maximalIdeal D.E.j‖ = ‖B.tateParameter b‖⁻¹ := by
    rw [← iutInitialThetaOddSupportBaseQPilotSource_tateJ_eq D b]
    exact (t.norm_tateJ (JoshiTeich.ReferenceIut.twelve_ne_zero b.1)).trans (by rw [hq])
  have hmap : R.completionMap s = iutEmbedCompletion (R.liesOver s) := rfl
  have hroot := congrArg norm (R.qroot_pow_eq s)
  rw [norm_pow, hmap, iutEmbedCompletion_norm_eq_pow] at hroot
  have hJ := iutEmbedCompletion_norm_eq_pow (R.liesOver s)
    (NumberField.FinitePlace.embedding b.1.maximalIdeal D.E.j)
  rw [iutEmbedCompletion_embedding, hj, inv_pow] at hJ
  exact (congrArg (fun x : ℝ => x⁻¹) hroot).trans hJ.symm

def iutInitialThetaRelativeQRootFactorAt
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) : ℝ :=
  ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot s‖ ^
    ((Arithmetic.localDeg v : ℝ) / Arithmetic.localDeg s.1)

theorem iutInitialThetaRelativeQRootFactorAt_eq_inverse_relativeFinrank
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hsv : Ideal.LiesOver s.1.maximalIdeal.asIdeal v.maximalIdeal.asIdeal) :
    letI := LocalCompletion.relativeAlgebra hsv
    iutInitialThetaRelativeQRootFactorAt D v s =
      ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot s‖ ^
        (1 / (Module.finrank
          (LocalCompletion.completionAt ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) v)
          (LocalCompletion.completionAt ↥D.prime.torsionField s.1) : ℝ)) := by
  letI := LocalCompletion.relativeAlgebra hsv
  rw [LocalCompletion.inverse_relativeFinrank_eq_localDeg_ratio hsv]
  rfl

theorem iutInitialThetaRelativeQRootFactorAt_mem_Ioo
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    iutInitialThetaRelativeQRootFactorAt D v s ∈ Set.Ioo (0 : ℝ) 1 := by
  have hn : 0 < ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot s‖ :=
    norm_pos_iff.mpr ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero s)
  have hv : (0 : ℝ) < Arithmetic.localDeg v := by exact_mod_cast Arithmetic.localDeg_pos v
  have hs : (0 : ℝ) < Arithmetic.localDeg s.1 := by exact_mod_cast Arithmetic.localDeg_pos s.1
  exact ⟨Real.rpow_pos_of_pos hn _,
    Real.rpow_lt_one hn.le (iutInitialThetaFullQRoot_norm_lt_one D s) (div_pos hv hs)⟩

theorem iutInitialThetaRelativeQRootFactorAt_negLog_eq_moduliJLog
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hsv : Ideal.LiesOver s.1.maximalIdeal.asIdeal v.maximalIdeal.asIdeal) :
    -Real.log (iutInitialThetaRelativeQRootFactorAt D v s) =
      Real.log ‖NumberField.FinitePlace.embedding v.maximalIdeal
        (⟨D.E.j, IntermediateField.mem_adjoin_simple_self ℚ D.E.j⟩ :
          ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))‖ / (2 * (D.prime.ℓ : ℝ)) := by
  let M := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)
  let j : M := ⟨D.E.j, IntermediateField.mem_adjoin_simple_self ℚ D.E.j⟩
  have hmap : algebraMap M ↥D.prime.torsionField j =
      algebraMap D.F ↥D.prime.torsionField D.E.j := by
    rw [IsScalarTower.algebraMap_apply M D.F ↥D.prime.torsionField]
    rfl
  have hJ := iutEmbedCompletion_norm_eq_pow hsv (NumberField.FinitePlace.embedding v.maximalIdeal j)
  rw [iutEmbedCompletion_embedding, hmap,
    ← iutInitialThetaFullQRoot_pow_norm_inv_eq_torsionJNorm D s] at hJ
  have hlog := congrArg Real.log hJ
  rw [Real.log_inv, Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  change -((2 * (D.prime.ℓ : ℝ)) *
      Real.log ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot s‖) =
    ((Arithmetic.relRamIdx s.1 v : ℝ) * Arithmetic.relInertDeg s.1 v) *
      Real.log ‖NumberField.FinitePlace.embedding v.maximalIdeal j‖ at hlog
  have hd : (Arithmetic.localDeg s.1 : ℝ) = (Arithmetic.localDeg v : ℝ) *
      ((Arithmetic.relRamIdx s.1 v : ℝ) * Arithmetic.relInertDeg s.1 v) := by
    exact_mod_cast Arithmetic.localDeg_eq_mul hsv
  have hv : (Arithmetic.localDeg v : ℝ) ≠ 0 := by exact_mod_cast (Arithmetic.localDeg_pos v).ne'
  have he : (Arithmetic.relRamIdx s.1 v : ℝ) ≠ 0 := by
    exact_mod_cast Arithmetic.relRamIdx_ne_zero hsv
  have hf : (Arithmetic.relInertDeg s.1 v : ℝ) ≠ 0 := by
    intro hf
    have hpos : (0 : ℝ) < Arithmetic.localDeg s.1 := by exact_mod_cast Arithmetic.localDeg_pos s.1
    rw [hd, hf, mul_zero, mul_zero] at hpos
    exact (lt_irrefl _ hpos)
  have hEll : (D.prime.ℓ : ℝ) ≠ 0 := by exact_mod_cast D.prime.ℓ_prime.ne_zero
  have hweight : (Arithmetic.localDeg v : ℝ) / Arithmetic.localDeg s.1 =
      1 / ((Arithmetic.relRamIdx s.1 v : ℝ) * Arithmetic.relInertDeg s.1 v) := by
    rw [hd]
    field_simp [hv, he, hf]
  rw [iutInitialThetaRelativeQRootFactorAt,
    Real.log_rpow (norm_pos_iff.mpr ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero s)), hweight]
  change -((1 / ((Arithmetic.relRamIdx s.1 v : ℝ) * Arithmetic.relInertDeg s.1 v)) *
      Real.log ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot s‖) =
    Real.log ‖NumberField.FinitePlace.embedding v.maximalIdeal j‖ / (2 * (D.prime.ℓ : ℝ))
  field_simp [he, hf, hEll]
  nlinarith [hlog]

theorem iutInitialThetaRelativeQRootFactorAt_eq_of_liesOver
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (s t : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hsv : Ideal.LiesOver s.1.maximalIdeal.asIdeal v.maximalIdeal.asIdeal)
    (htv : Ideal.LiesOver t.1.maximalIdeal.asIdeal v.maximalIdeal.asIdeal) :
    iutInitialThetaRelativeQRootFactorAt D v s = iutInitialThetaRelativeQRootFactorAt D v t := by
  apply Real.log_injOn_pos (iutInitialThetaRelativeQRootFactorAt_mem_Ioo D v s).1
    (iutInitialThetaRelativeQRootFactorAt_mem_Ioo D v t).1
  have hs := iutInitialThetaRelativeQRootFactorAt_negLog_eq_moduliJLog D v s hsv
  have ht := iutInitialThetaRelativeQRootFactorAt_negLog_eq_moduliJLog D v t htv
  linarith

theorem iutInitialThetaRelativeQRootFactorAt_eq_selectedFactor
    (v : iutInitialThetaOddModSupportFinset D)
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hsv : Ideal.LiesOver s.1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal) :
    iutInitialThetaRelativeQRootFactorAt D v.1 s = iutInitialThetaRelativeQRootFactor D v := by
  rw [iutInitialThetaRelativeQRootFactor_eq_localDeg_ratio]
  exact iutInitialThetaRelativeQRootFactorAt_eq_of_liesOver D v.1 s
    (iutInitialThetaModuliSelectedSourceEquiv D v).1 hsv
    (iutInitialThetaModuliSelectedSource_liesOver D v)

end
end JoshiTeich.Act1Scene1
