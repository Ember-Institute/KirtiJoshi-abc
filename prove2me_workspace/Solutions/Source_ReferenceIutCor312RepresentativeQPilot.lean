import Solutions.Source_ReferenceIutConcreteThetaRegion
import Solutions.Source_ReferenceIutCor312QPilotModuli
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.ThetaLocalData

open NumberField WeierstrassCurve
open scoped BigOperators

universe u v

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {D : InitialThetaData AG TG} {LT : LocalTheory.{u, v} D.Kt}
variable (TL : ThetaLocalData D LT)

private theorem log_norm_qroot_eq_neg_torsion_jLog
    {w : FinitePlace D.Kt} {b : FinitePlace D.F}
    (hwb : FinitePlace.LiesOver w b) (hb : b ∈ badPlacesOver D.F D.E D.VBad) :
    Real.log ‖TL.qroot w‖ =
      -Real.log (w (algebraMap D.F D.Kt D.E.j)) / (2 * (D.ℓ : ℝ)) := by
  have hdeg : (localDeg D.Kt w : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (LT.localDeg_pos w).ne'
  have hp : (residueChar w).Prime := Tripod.residueChar_prime w
  have hlog : Real.log (residueChar w) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hram : (ramIdx D.F b : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Tripod.ramIdx_pos' b).ne'
  have hell : (D.ℓ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr D.prime.ℓ_prime.ne_zero
  have hdegree : (localDeg D.Kt w : ℝ) =
      (ramIdx D.F b : ℝ) * inertDeg D.F b * Tripod.relLocalDeg w b := by
    have hnat : localDeg D.Kt w = (ramIdx D.F b * inertDeg D.F b) * Tripod.relLocalDeg w b :=
      Tripod.localDeg_eq_mul hwb
    exact_mod_cast hnat
  have hchar : residueChar w = residueChar b := Tripod.residueChar_eq_of_liesOver hwb
  have hroot := TL.ordp_qroot w b hwb hb
  rw [ordp, div_eq_iff (mul_ne_zero hdeg hlog)] at hroot
  calc
    Real.log ‖TL.qroot w‖ =
        -(((D.prime.qOrder b hb : ℝ) / (2 * D.ℓ * ramIdx D.F b)) *
          ((localDeg D.Kt w : ℝ) * Real.log (residueChar w))) := by
      rw [← hroot, neg_neg]
    _ = _ := by
      rw [Tripod.apply_algebraMap_eq_pow hwb, Real.log_pow, D.log_j_eq_qOrder b hb,
        hdegree, hchar]
      field_simp [hell, hram]

/-- The relative-degree weighted log of a root at any place over a bad moduli place. -/
theorem log_norm_qroot_div_relLocalDeg
    (hModuli : @algebraMap ↥(fieldOfModuli D.F D.E) D.Kt _ _ D.algebraModK =
      (algebraMap D.F D.Kt).comp (algebraMap ↥(fieldOfModuli D.F D.E) D.F))
    {w : FinitePlace D.Kt} {v : FinitePlace ↥(fieldOfModuli D.F D.E)}
    (hv : v ∈ D.VBad) (hwv : @FinitePlace.LiesOver _ _ _ _ _ _ D.algebraModK w v) :
    letI : Algebra ↥(fieldOfModuli D.F D.E) D.Kt := D.algebraModK
    Real.log ‖TL.qroot w‖ / (Tripod.relLocalDeg w v : ℝ) =
      -Real.log (v D.moduliJ) / (2 * (D.ℓ : ℝ)) := by
  let M := ↥(fieldOfModuli D.F D.E)
  let _ : Algebra M D.Kt := D.algebraModK
  have hmap : algebraMap M D.Kt = (algebraMap D.F D.Kt).comp (algebraMap M D.F) :=
    hModuli
  let _ : IsScalarTower (𝓞 M) (𝓞 D.F) (𝓞 D.Kt) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      apply RingOfIntegers.coe_injective
      exact RingHom.congr_fun hmap x)
  let b : FinitePlace D.F := Tripod.placeUnder (k := D.F) w
  have hwb : FinitePlace.LiesOver w b := Tripod.liesOver_placeUnder w
  have hbv : FinitePlace.LiesOver b v := by
    have : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hwv
    have : w.maximalIdeal.asIdeal.LiesOver b.maximalIdeal.asIdeal := hwb
    exact Ideal.LiesOver.tower_bot w.maximalIdeal.asIdeal b.maximalIdeal.asIdeal
      v.maximalIdeal.asIdeal
  have hb : b ∈ badPlacesOver D.F D.E D.VBad := ⟨v, hv, hbv⟩
  have hj : algebraMap M D.Kt D.moduliJ = algebraMap D.F D.Kt D.E.j :=
    RingHom.congr_fun hmap D.moduliJ
  have hell : (D.ℓ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr D.prime.ℓ_prime.ne_zero
  have hrel : (Tripod.relLocalDeg w v : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Tripod.relLocalDeg_ne_zero hwv)
  change Real.log ‖TL.qroot w‖ / (Tripod.relLocalDeg w v : ℝ) = _
  rw [TL.log_norm_qroot_eq_neg_torsion_jLog hwb hb, ← hj,
    Tripod.apply_algebraMap_eq_pow hwv, Real.log_pow]
  field_simp [hell, hrel]

/-- The signed q-pilot equals the relative-degree weighted log sum at the selected
places, divided by the absolute degree of the moduli field. -/
theorem qPilot_lhs_eq_sum_section_log_norm (QI : QPilotInputs D)
    (hModuli : @algebraMap ↥(fieldOfModuli D.F D.E) D.Kt _ _ D.algebraModK =
      (algebraMap D.F D.Kt).comp (algebraMap ↥(fieldOfModuli D.F D.E) D.F)) :
    letI : Algebra ↥(fieldOfModuli D.F D.E) D.Kt := D.algebraModK
    (concreteVariantData D LT TL QI).qPilot.lhs =
      (∑ v ∈ QI.badModuliFinset,
        Real.log ‖TL.qroot (D.localData.sect.sectFin v)‖ /
          (Tripod.relLocalDeg (D.localData.sect.sectFin v) v : ℝ)) /
        (Module.finrank ℚ ↥(fieldOfModuli D.F D.E) : ℝ) := by
  let _ : Algebra ↥(fieldOfModuli D.F D.E) D.Kt := D.algebraModK
  change QI.qPilot.lhs = _
  rw [QI.lhs_eq_neg_moduli_jLogSum]
  calc
    _ = (∑ v ∈ QI.badModuliFinset, -Real.log (v D.moduliJ) / (2 * (D.ℓ : ℝ))) /
          (Module.finrank ℚ ↥(fieldOfModuli D.F D.E) : ℝ) := by
      rw [← Finset.sum_div, Finset.sum_neg_distrib]
      ring
    _ = _ := by
      refine congrArg (fun x : ℝ => x / _) (Finset.sum_congr rfl fun v hv => ?_)
      exact (TL.log_norm_qroot_div_relLocalDeg hModuli (QI.mem_badModuliFinset.mp hv)
        (D.localData.sect.sectFin_liesOver v)).symm

end AbcAdaptation.Reference.Iut.ThetaLocalData
