import Solutions.Source_JoshiIINormalizedSquareLogs
import Solutions.Source_ReferenceIutCor312RepresentativeQPilot

/-!
Use the normalized square exponents of Joshi II, Theorem 9.2.1, with the
representative q-root logs and degree weights of the concrete P7 data.
-/

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.ThetaLocalData

open NumberField
open scoped BigOperators

universe u v

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {D : InitialThetaData AG TG} {LT : LocalTheory.{u, v} D.Kt}
variable (TL : ThetaLocalData D LT)

/-- The average of the normalized square-scaled, degree-weighted
representative q-root logs. -/
noncomputable def normalizedWitnessLogAverage (QI : QPilotInputs D) : ℝ :=
  let M := ↥(fieldOfModuli D.F D.E)
  letI : Algebra M D.Kt := D.algebraModK
  let m := (D.ℓ - 1) / 2
  (∑ j : Fin m, ∑ w ∈ QI.badModuliFinset,
    (1 / ((Tripod.relLocalDeg (D.localData.sect.sectFin w) w : ℝ) *
      (Module.finrank ℚ M : ℝ))) *
      ((((j : ℝ) + 1) / (m : ℝ)) ^ 2 * Real.log ‖TL.qroot (D.localData.sect.sectFin w)‖)) /
    (m : ℝ)

private theorem qPilot_lhs_neg (QI : QPilotInputs D) :
    QI.qPilot.lhs < 0 := by
  obtain ⟨v, hv⟩ := D.global.bad_nonempty
  obtain ⟨w, hw⟩ := JoshiTeich.ReferenceIut.FinitePlace.exists_liesOver (K := D.F) v
  have hwFin : w ∈ QI.qPilot.badFinset :=
    (Set.ext_iff.mp QI.qPilot.badFinset_spec w).mpr ⟨v, hv, hw⟩
  have hterm (b : {b // b ∈ QI.qPilot.badFinset}) :
      0 < QI.qPilot.weight b.1 * (D.prime.qOrder b.1 (QI.qPilot.mem_bad b.2) : ℝ) *
        Real.log (residueChar b.1) := by
    have hb := QI.qPilot.mem_bad b.2
    have horder : 0 < D.prime.qOrder b.1 hb :=
      ((D.prime.tate b.1 hb).toOrdered (D.prime.unif_isUniformizer b.1 hb)).orderNat_pos
    have hp := Tripod.residueChar_prime b.1
    exact mul_pos (mul_pos (QI.qPilot.weight_pos b.1 b.2) (by exact_mod_cast horder))
      (Real.log_pos (by exact_mod_cast hp.one_lt))
  have hlog : 0 < QI.qPilot.logQ := by
    unfold QPilotData.logQ
    refine Finset.sum_pos' (fun b _ => (hterm b).le) ?_
    exact ⟨⟨w, hwFin⟩, Finset.mem_attach _ _, hterm ⟨w, hwFin⟩⟩
  have hℓ : (0 : ℝ) < (D.ℓ : ℝ) := by exact_mod_cast D.prime.ℓ_prime.pos
  exact neg_lt_zero.mpr (div_pos hlog (mul_pos (by norm_num) hℓ))

/-- With compatible moduli algebra maps, the P7 signed q-pilot is strictly
below the average with normalized square exponents. -/
theorem qPilot_lhs_lt_normalizedWitnessLogAverage (QI : QPilotInputs D)
    (hModuli : @algebraMap ↥(fieldOfModuli D.F D.E) D.Kt _ _ D.algebraModK =
      (algebraMap D.F D.Kt).comp (algebraMap ↥(fieldOfModuli D.F D.E) D.F)) :
    (concreteVariantData D LT TL QI).qPilot.lhs < TL.normalizedWitnessLogAverage QI := by
  let M := ↥(fieldOfModuli D.F D.E)
  letI : Algebra M D.Kt := D.algebraModK
  let weight (w : FinitePlace M) : ℝ :=
    1 / ((Tripod.relLocalDeg (D.localData.sect.sectFin w) w : ℝ) * (Module.finrank ℚ M : ℝ))
  let rootLog (w : FinitePlace M) : ℝ := Real.log ‖TL.qroot (D.localData.sect.sectFin w)‖
  have hsum : (concreteVariantData D LT TL QI).qPilot.lhs =
      ∑ w ∈ QI.badModuliFinset, weight w * rootLog w := by
    rw [TL.qPilot_lhs_eq_sum_section_log_norm QI hModuli, Finset.sum_div]
    refine Finset.sum_congr rfl fun w _ => ?_
    dsimp only [weight, rootLog]
    rw [div_div, one_div_mul_eq_div]
  have hnegative : (∑ w ∈ QI.badModuliFinset, weight w * rootLog w) < 0 := by
    rw [← hsum]
    exact qPilot_lhs_neg QI
  have hm : 2 ≤ (D.ℓ - 1) / 2 := by
    have hℓ := D.prime.five_le
    change 5 ≤ D.ℓ at hℓ
    omega
  rw [hsum]
  exact JoshiII.weighted_root_log_sum_lt_normalized_average QI.badModuliFinset weight rootLog
    hm hnegative

/-- A comparison of the normalized witness average with the actual hull
right-hand side suffices for the Corollary 3.12 variant on the same data. -/
theorem corollary312Variant_of_normalizedWitnessLogAverage_le_rhs (QI : QPilotInputs D)
    (hModuli : @algebraMap ↥(fieldOfModuli D.F D.E) D.Kt _ _ D.algebraModK =
      (algebraMap D.F D.Kt).comp (algebraMap ↥(fieldOfModuli D.F D.E) D.F))
    (hvolume : TL.normalizedWitnessLogAverage QI ≤ (concreteVariantData D LT TL QI).rhsData.rhs) :
    Corollary312Variant (concreteVariantData D LT TL QI) :=
  (TL.qPilot_lhs_lt_normalizedWitnessLogAverage QI hModuli).le.trans hvolume

end AbcAdaptation.Reference.Iut.ThetaLocalData

#print axioms AbcAdaptation.Reference.Iut.ThetaLocalData.qPilot_lhs_lt_normalizedWitnessLogAverage
#print axioms AbcAdaptation.Reference.Iut.ThetaLocalData.corollary312Variant_of_normalizedWitnessLogAverage_le_rhs
