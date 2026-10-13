import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRepresentativeCoefficients
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedPaperBallProduct
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionRelativeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
source-id: JT-SCENE1-INITIAL-THETA-RELATIVE-QROOT-FACTOR
source: actual section representatives, relative completion degrees, the
ramification tower and complete moduli j-log accounting; Joshi III eq:weights.
fidelity: constructs each factor from the actual inverse relative completion
dimension and raw root norm. Dividing its negative logarithm by the moduli
global degree gives the actual normalized moduli j-log term. No paper carrier,
norm, hull or presentation-independent tensor volume is identified.
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

theorem iutInitialThetaModuliSelectedSource_liesOver (v : iutInitialThetaOddModSupportFinset D) :
    Ideal.LiesOver (iutInitialThetaModuliSelectedSourceEquiv D v).1.1.maximalIdeal.asIdeal
      v.1.maximalIdeal.asIdeal := by
  change Ideal.LiesOver (iutInitialThetaFinitePlaceSection D v.1).maximalIdeal.asIdeal
    v.1.maximalIdeal.asIdeal
  exact iutInitialThetaFinitePlaceSection_liesOver D v.1

theorem iutInitialThetaRepresentativeCoefficient_mul_ramIdx_eq_localDeg_div_finrank
    (v : iutInitialThetaOddModSupportFinset D) :
    let s := (iutInitialThetaModuliSelectedSourceEquiv D v).1
    iutInitialThetaRepresentativeCoefficient D v * (Arithmetic.ramIdx s.1 : ℝ) =
      (Arithmetic.localDeg v.1 : ℝ) /
        Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) := by
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let s := (iutInitialThetaModuliSelectedSourceEquiv D v).1
  let b := R.basePlace s
  have hb : b.1 = iutInitialThetaSectionBasePlace D v.1 :=
    iutInitialThetaOddSupportSelectedQRootPlace_basePlace_eq_sectionBasePlace D v.1
      ((iutInitialThetaOddModSupport_finite D).mem_toFinset.mp v.2)
  have hbv : Ideal.LiesOver b.1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal := by
    rw [hb]
    exact iutInitialThetaSectionBasePlace_liesOver D v.1
  have hsb := Arithmetic.ramIdx_eq_mul (R.liesOver s)
  have hbvRam := Arithmetic.ramIdx_eq_mul hbv
  have he : (Arithmetic.relRamIdx b.1 v.1 : ℝ) ≠ 0 := by
    exact_mod_cast Arithmetic.relRamIdx_ne_zero hbv
  have hr : (Arithmetic.relRamIdx s.1 b.1 : ℝ) ≠ 0 := by
    exact_mod_cast Arithmetic.relRamIdx_ne_zero (R.liesOver s)
  have hM : (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ) ≠ 0 :=
    ne_of_gt Arithmetic.finrank_pos
  unfold iutInitialThetaRepresentativeCoefficient Arithmetic.qPilotWeight Arithmetic.localDeg
  change ((Arithmetic.inertDeg v.1 : ℝ) /
      Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) /
        ((Arithmetic.relRamIdx b.1 v.1 : ℝ) * Arithmetic.relRamIdx s.1 b.1)) *
          Arithmetic.ramIdx s.1 = _
  rw [hsb, hbvRam]
  push_cast
  field_simp [he, hr, hM]
  <;> ring

/-- A raw root norm with the actual inverse relative completion degree. -/
def iutInitialThetaRelativeQRootFactor (v : iutInitialThetaOddModSupportFinset D) : ℝ :=
  let s := (iutInitialThetaModuliSelectedSourceEquiv D v).1
  letI := LocalCompletion.relativeAlgebra (iutInitialThetaModuliSelectedSource_liesOver D v)
  ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot s‖ ^
    (1 / (Module.finrank
      (LocalCompletion.completionAt ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) v.1)
      (LocalCompletion.completionAt ↥D.prime.torsionField s.1) : ℝ))

theorem iutInitialThetaRelativeQRootFactor_eq_localDeg_ratio
    (v : iutInitialThetaOddModSupportFinset D) :
    let s := (iutInitialThetaModuliSelectedSourceEquiv D v).1
    iutInitialThetaRelativeQRootFactor D v =
      ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot s‖ ^
        ((Arithmetic.localDeg v.1 : ℝ) / Arithmetic.localDeg s.1) := by
  let s := (iutInitialThetaModuliSelectedSourceEquiv D v).1
  letI := LocalCompletion.relativeAlgebra (iutInitialThetaModuliSelectedSource_liesOver D v)
  change ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot s‖ ^
    (1 / (Module.finrank
      (LocalCompletion.completionAt ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) v.1)
      (LocalCompletion.completionAt ↥D.prime.torsionField s.1) : ℝ)) = _
  rw [LocalCompletion.inverse_relativeFinrank_eq_localDeg_ratio
    (iutInitialThetaModuliSelectedSource_liesOver D v)]

theorem iutInitialThetaRelativeQRootFactor_mem_Ioo
    (v : iutInitialThetaOddModSupportFinset D) :
    iutInitialThetaRelativeQRootFactor D v ∈ Set.Ioo (0 : ℝ) 1 := by
  rw [iutInitialThetaRelativeQRootFactor_eq_localDeg_ratio]
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let s := (iutInitialThetaModuliSelectedSourceEquiv D v).1
  have hn : 0 < ‖R.qroot s‖ := norm_pos_iff.mpr (R.qroot_ne_zero s)
  have hv : (0 : ℝ) < Arithmetic.localDeg v.1 := by exact_mod_cast Arithmetic.localDeg_pos v.1
  have hs : (0 : ℝ) < Arithmetic.localDeg s.1 := by exact_mod_cast Arithmetic.localDeg_pos s.1
  exact ⟨Real.rpow_pos_of_pos hn _,
    Real.rpow_lt_one hn.le (iutInitialThetaFullQRoot_norm_lt_one D s) (div_pos hv hs)⟩

theorem iutInitialThetaRelativeQRootFactor_negLog_div_eq_moduliJLogTerm
    (v : iutInitialThetaOddModSupportFinset D) :
    -Real.log (iutInitialThetaRelativeQRootFactor D v) /
        Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) =
      Real.log ‖NumberField.FinitePlace.embedding v.1.maximalIdeal
        (⟨D.E.j, IntermediateField.mem_adjoin_simple_self ℚ D.E.j⟩ :
          ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))‖ /
        (2 * (D.prime.ℓ : ℝ) *
          Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) := by
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let s := (iutInitialThetaModuliSelectedSourceEquiv D v).1
  have hcoef := iutInitialThetaRepresentativeCoefficient_mul_ramIdx_eq_localDeg_div_finrank D v
  have hj := iutInitialThetaModuliJLogTerm_eq_coefficient_mul_selectedPaperTerm D v
  have hs : (Arithmetic.localDeg s.1 : ℝ) ≠ 0 := by
    exact_mod_cast (Arithmetic.localDeg_pos s.1).ne'
  have hp : Real.log (Arithmetic.residueChar s.1) ≠ 0 := (Real.log_pos
    (by exact_mod_cast (Arithmetic.residueChar_prime s.1).one_lt)).ne'
  have hM : (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ) ≠ 0 :=
    ne_of_gt Arithmetic.finrank_pos
  rw [iutInitialThetaRelativeQRootFactor_eq_localDeg_ratio,
    Real.log_rpow (norm_pos_iff.mpr (R.qroot_ne_zero s)), hj]
  calc
    _ = ((Arithmetic.localDeg v.1 : ℝ) /
        Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) *
          Arithmetic.ordp s.1 (R.qroot s) * Real.log (Arithmetic.residueChar s.1) := by
      change -((Arithmetic.localDeg v.1 : ℝ) / Arithmetic.localDeg s.1 * Real.log ‖R.qroot s‖) /
          Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) = _
      unfold Arithmetic.ordp
      field_simp [hs, hp, hM]
      <;> ring
    _ = _ := by
      rw [← hcoef]
      ring

end
end JoshiTeich.Act1Scene1
