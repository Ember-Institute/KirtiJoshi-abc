import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedSupportDefect
import ArithmeticTeichmullerSpaces.Act1Scene1.IutCompletionLogAccounting

/-!
source-id: JT-SCENE1-INITIAL-THETA-QPILOT-JLOG
source: the actual base Tate j-identity and norm_tateJ, completion norm/order
normalization, and the complete finite-place fibre degree formula.
fidelity: removes the chosen Tate parameter from the numerical q-pilot term
and proves global-degree normalized log accounting over complete fibres.
No section coverage, Galois assumption, or theta-volume estimate is added.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators

universe u
noncomputable section

theorem iutNormalizedLog_norm_embedding_sum_liesOver
    {F K : Type u} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    (x : F) (w : NumberField.FinitePlace F) (s : Finset (NumberField.FinitePlace K))
    (hs : ∀ v, v ∈ s ↔ Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal) :
    (∑ v ∈ s, Real.log ‖NumberField.FinitePlace.embedding v.maximalIdeal (algebraMap F K x)‖) /
        (Module.finrank ℚ K : ℝ) =
      Real.log ‖NumberField.FinitePlace.embedding w.maximalIdeal x‖ / (Module.finrank ℚ F : ℝ) := by
  let : IsScalarTower ℚ F K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have h := iutNegLog_norm_embedding_sum_liesOver x w s hs
  rw [Finset.sum_neg_distrib] at h
  have hsum : (∑ v ∈ s, Real.log ‖NumberField.FinitePlace.embedding v.maximalIdeal (algebraMap F K x)‖) =
      (Module.finrank F K : ℝ) * Real.log ‖NumberField.FinitePlace.embedding w.maximalIdeal x‖ := by
    linarith
  have hrank : (Module.finrank ℚ K : ℝ) = (Module.finrank ℚ F : ℝ) * (Module.finrank F K : ℝ) := by
    exact_mod_cast (Module.finrank_mul_finrank ℚ F K).symm
  have hne : (Module.finrank F K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := F) (M := K)).ne'
  have hFne : (Module.finrank ℚ F : ℝ) ≠ 0 := ne_of_gt Arithmetic.finrank_pos
  rw [hsum, hrank]
  field_simp [hne, hFne]

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

theorem iutInitialThetaBaseQPilotLogTerm_eq_jLog
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset) :
    iutInitialThetaBaseQPilotLogTerm D b =
      Real.log ‖NumberField.FinitePlace.embedding b.1.maximalIdeal D.E.j‖ /
        (2 * (D.prime.ℓ : ℝ) * (Module.finrank ℚ D.F : ℝ)) := by
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let t := iutInitialThetaOddSupportBaseTateParameterAtCurvePlace D b.1 (B.mem_badPlaces b)
  have hq : (t.q : b.1.maximalIdeal.adicCompletion D.F) = B.tateParameter b := rfl
  have hj : ‖NumberField.FinitePlace.embedding b.1.maximalIdeal D.E.j‖ = ‖B.tateParameter b‖⁻¹ := by
    rw [← iutInitialThetaOddSupportBaseQPilotSource_tateJ_eq D b]
    exact (t.norm_tateJ (JoshiTeich.ReferenceIut.twelve_ne_zero b.1)).trans (by rw [hq])
  have hnorm := Arithmetic.completionNorm_eq_residueChar_pow_neg_qOrder b.1 (B.tateParameter b)
    (B.tateParameter_ne_zero b) (B.tateParameter_norm_lt_one b)
  have hlog : Real.log ‖NumberField.FinitePlace.embedding b.1.maximalIdeal D.E.j‖ =
      (B.qOrder b : ℝ) * (Arithmetic.inertDeg b.1 : ℝ) * Real.log (Arithmetic.residueChar b.1) := by
    rw [hj, Real.log_inv, hnorm, Real.log_zpow, Real.log_pow]
    rw [show Arithmetic.completionQOrder b.1 (B.tateParameter b) = B.qOrder b from rfl]
    push_cast
    ring
  rw [hlog]
  unfold iutInitialThetaBaseQPilotLogTerm Arithmetic.qPilotWeight
  change ((Arithmetic.inertDeg b.1 : ℝ) / (Module.finrank ℚ D.F : ℝ)) *
    ((B.qOrder b : ℝ) / (2 * (D.prime.ℓ : ℝ))) * Real.log (Arithmetic.residueChar b.1) = _
  ring

theorem iutInitialThetaFullBaseQPilotLogSum_eq_jLogSum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    iutInitialThetaFullBaseQPilotLogSum D =
      (∑ b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset,
        Real.log ‖NumberField.FinitePlace.embedding b.1.maximalIdeal D.E.j‖) /
          (2 * (D.prime.ℓ : ℝ) * (Module.finrank ℚ D.F : ℝ)) := by
  unfold iutInitialThetaFullBaseQPilotLogSum
  calc
    _ = ∑ b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset,
        Real.log ‖NumberField.FinitePlace.embedding b.1.maximalIdeal D.E.j‖ /
          (2 * (D.prime.ℓ : ℝ) * (Module.finrank ℚ D.F : ℝ)) := by
      apply Finset.sum_congr rfl
      intro b hb
      exact iutInitialThetaBaseQPilotLogTerm_eq_jLog D b
    _ = _ := (Finset.sum_div _ _ _).symm

/-- Complete fibres of the actual moduli j-invariant retain all base places.
The finite enumeration is explicit; section coverage is not required. -/
theorem iutInitialThetaModuliJ_normalized_fiber
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (s : Finset (NumberField.FinitePlace D.F))
    (hs : ∀ w, w ∈ s ↔ Ideal.LiesOver w.maximalIdeal.asIdeal v.maximalIdeal.asIdeal) :
    (∑ w ∈ s, Real.log ‖NumberField.FinitePlace.embedding w.maximalIdeal D.E.j‖) /
        (Module.finrank ℚ D.F : ℝ) =
      Real.log ‖NumberField.FinitePlace.embedding v.maximalIdeal
        (⟨D.E.j, IntermediateField.mem_adjoin_simple_self ℚ D.E.j⟩ :
          ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))‖ /
        (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ) := by
  exact iutNormalizedLog_norm_embedding_sum_liesOver
    (F := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) (K := D.F)
    ⟨D.E.j, IntermediateField.mem_adjoin_simple_self ℚ D.E.j⟩ v s hs

end
end JoshiTeich.Act1Scene1
