import Solutions.Source_ReferenceIutPointModuliMap
import Solutions.Source_TripodRationalLegendreFiveP7Counterexample
import ArithmeticTeichmullerSpaces.Prologue.Audit.Checks
import ArithmeticTeichmullerSpaces.Prologue.Audit.ImportAudit
import ArithmeticTeichmullerSpaces.Act1Scene1
import ArithmeticTeichmullerSpaces.Prologue.Audit.AxiomAudit
import Solutions.Source_ReferenceIutCor312RepresentativeQPilot
import Theorems.Thm_AbcAdaptation_Reference_Iut_sum_affine_quadratic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
The coefficient calculation in Kirti Joshi, Arithmetic Teichmuller Spaces II,
Theorem 9.2.1, proof after `eq:val-rel-main2`. The signed weighted average uses
the same normalized square exponents and works for a finite set of places.
-/

set_option autoImplicit false

namespace AbcAdaptation.JoshiII

open scoped BigOperators

/-- The sum of the squared normalized labels for a positive procession length. -/
theorem sum_normalized_squares (m : ℕ) (hm : 0 < m) :
    (∑ j : Fin m, (((j : ℝ) + 1) / (m : ℝ)) ^ 2) =
      ((m : ℝ) + 1) * (2 * (m : ℝ) + 1) / (6 * (m : ℝ)) := by
  have hsum : (∑ j : Fin m, ((j : ℝ) + 1) ^ 2) =
      (m : ℝ) * ((m : ℝ) + 1) * (2 * (m : ℝ) + 1) / 6 := by
    simpa only [zero_mul, one_mul, zero_add, add_zero] using
      Reference.Iut.sum_affine_quadratic m 0 1 0
  simp_rw [div_pow]
  rw [← Finset.sum_div, hsum]
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  field_simp [hm0] <;> ring

/-- Substitute the log of a `2ℓ`-th root, where `ℓ = 2m + 1`. -/
theorem sum_normalized_square_root_logs (m : ℕ) (hm : 0 < m) (qLog : ℝ) :
    (∑ j : Fin m, (((j : ℝ) + 1) / (m : ℝ)) ^ 2 *
        (qLog / (2 * (2 * (m : ℝ) + 1)))) =
      (1 / 12 : ℝ) * (1 + 1 / (m : ℝ)) * qLog := by
  rw [← Finset.sum_mul, sum_normalized_squares m hm]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hℓ : (0 : ℝ) < 2 * (m : ℝ) + 1 := by linarith
  field_simp [hmR.ne', hℓ.ne'] <;> ring

private theorem normalized_square_sum_lt_length {m : ℕ} (hm : 2 ≤ m) :
    ((m : ℝ) + 1) * (2 * (m : ℝ) + 1) / (6 * (m : ℝ)) < (m : ℝ) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  apply (div_lt_iff₀ (mul_pos (by norm_num) hm0)).2
  have hgap : 0 < ((m : ℝ) - 1) * (4 * (m : ℝ) + 1) :=
    mul_pos (by linarith) (by linarith)
  nlinarith only [hgap]

/-- The reference log bound is strict for a negative Tate log and `ℓ ≥ 5` odd. -/
theorem root_log_bound_lt_sum_normalized_square_root_logs {m : ℕ}
    (hm : 2 ≤ m) {qLog : ℝ} (hq : qLog < 0) :
    (m : ℝ) * (qLog / (2 * (2 * (m : ℝ) + 1))) <
      ∑ j : Fin m, (((j : ℝ) + 1) / (m : ℝ)) ^ 2 *
        (qLog / (2 * (2 * (m : ℝ) + 1))) := by
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hℓ : (0 : ℝ) < 2 * (2 * (m : ℝ) + 1) := by linarith
  rw [← Finset.sum_mul, sum_normalized_squares m hm0]
  exact mul_lt_mul_of_neg_right (normalized_square_sum_lt_length hm) (div_neg_of_neg_of_pos hq hℓ)

/-- A negative signed sum of root logs lies below its normalized square-weighted
average. The place weights are the same on the two sides. -/
theorem weighted_root_log_sum_lt_normalized_average {ι : Type*}
    (s : Finset ι) (weight rootLog : ι → ℝ) {m : ℕ} (hm : 2 ≤ m)
    (hnegative : (∑ v ∈ s, weight v * rootLog v) < 0) :
    (∑ v ∈ s, weight v * rootLog v) <
      (∑ j : Fin m, ∑ v ∈ s, weight v * ((((j : ℝ) + 1) / (m : ℝ)) ^ 2 * rootLog v)) /
        (m : ℝ) := by
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hfactor :
      (∑ j : Fin m, ∑ v ∈ s, weight v * ((((j : ℝ) + 1) / (m : ℝ)) ^ 2 * rootLog v)) =
        (∑ j : Fin m, (((j : ℝ) + 1) / (m : ℝ)) ^ 2) *
          (∑ v ∈ s, weight v * rootLog v) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [hfactor, sum_normalized_squares m hm0]
  apply (lt_div_iff₀ hmR).2
  rw [mul_comm (∑ v ∈ s, weight v * rootLog v) (m : ℝ)]
  exact mul_lt_mul_of_neg_right (normalized_square_sum_lt_length hm) hnegative

end AbcAdaptation.JoshiII

#print axioms AbcAdaptation.JoshiII.sum_normalized_squares
#print axioms AbcAdaptation.JoshiII.sum_normalized_square_root_logs
#print axioms AbcAdaptation.JoshiII.root_log_bound_lt_sum_normalized_square_root_logs
#print axioms AbcAdaptation.JoshiII.weighted_root_log_sum_lt_normalized_average


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

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open Reference.Iut

variable {AG : AnabelianGeometry.{0}} {TG : TemperedGeometry AG}

/-- On the actual P7 data, the normalized witness average uses the same chosen
point, prime, local theory, root family, and q-pilot inputs. -/
theorem exists_normalizedWitnessLogAverage_of_sourceP7 {K : CompactlyBounded} {d : ℕ}
    (CI : CurveInputs tripodTheory AG K d) (anab : AnabelianExistence AG TG)
    {X : Corollary312VariantData.{0, 0} AG TG} (hX : IsSourceP7Variant CI anab X) :
    ∃ (D : InitialThetaData AG TG) (LT : LocalTheory.{0, 0} D.Kt)
      (TL : ThetaLocalData D LT) (QI : QPilotInputs D),
      X = concreteVariantData D LT TL QI ∧ X.qPilot.lhs < TL.normalizedWitnessLogAverage QI := by
  rcases hX with ⟨x, hx, hxe, ℓ, hprime, h7, hP2, _, hP5, hsl, htwo, hEq⟩
  let P := CI.pointThetaData anab x hx hxe ℓ hprime h7 hP2 hP5 hsl
  let TL := (P.localThetaData htwo).withBadChars P.qPilotInputs
  refine ⟨P.data, P.localTheory, TL, P.qPilotInputs, hEq, ?_⟩
  rw [hEq]
  exact TL.qPilot_lhs_lt_normalizedWitnessLogAverage P.qPilotInputs
    (CI.pointThetaData_algebraMap_moduli_torsion anab x hx hxe ℓ hprime h7 hP2 hP5 hsl)

/-- The degree-one Legendre counterexample has hull volume strictly below the
normalized numerical witness from the same P7 data. -/
theorem exists_sourceP7Hull_lt_normalizedWitnessLogAverage_rationalLegendreFiveLocus
    (P : CurveProviders) (hcore : CoreFinitenessHyp P rationalLegendreFiveLocus 1 AG)
    (anab : AnabelianExistence AG TG) :
    let K := rationalLegendreFiveLocus
    let CF : CurveFactsProp P K 1
        (cyclicConst K (torsionConst K.c (legendre_torsion_x_le K.c))) := ⟨cyclicBoundOdd P K 1⟩
    let CI := curveInputs_from_source P K 1 CF hcore northcottHyp
      (legendreHeight P K) (twoAdicBound P K)
    ∃ (D : InitialThetaData AG TG) (LT : LocalTheory.{0, 0} D.Kt)
      (TL : ThetaLocalData D LT) (QI : QPilotInputs D),
      let X := concreteVariantData D LT TL QI
      IsSourceP7Variant CI anab X ∧ X.rhsData.rhs < TL.normalizedWitnessLogAverage QI := by
  intro K CF CI
  obtain ⟨X, hX, hRhs⟩ := exists_sourceP7Counterexample_rationalLegendreFiveLocus P hcore anab
  obtain ⟨D, LT, TL, QI, rfl, hQ⟩ := exists_normalizedWitnessLogAverage_of_sourceP7 CI anab hX
  exact ⟨D, LT, TL, QI, hX, hRhs.trans hQ⟩

end AbcAdaptation.Tripod

#print axioms AbcAdaptation.Tripod.exists_normalizedWitnessLogAverage_of_sourceP7
#print axioms AbcAdaptation.Tripod.exists_sourceP7Hull_lt_normalizedWitnessLogAverage_rationalLegendreFiveLocus
