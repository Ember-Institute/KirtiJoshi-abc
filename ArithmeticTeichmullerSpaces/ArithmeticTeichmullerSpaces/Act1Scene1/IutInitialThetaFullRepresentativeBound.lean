import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaModuliJAccounting

/-!
source-id: JT-SCENE1-INITIAL-THETA-FULL-REPRESENTATIVE-BOUND
source: actual full moduli j-log accounting, complete-fibre normalization,
the selected q-root ordp identity, and the ramification/inertia tower laws.
fidelity: bounds the actual full odd-support q-pilot by the selected paper
sum without section coverage. The full fibre contribution is compared with
one actual representative using its relative ramification and the moduli
q-pilot weight. Paper carrier identity and theta-volume remain separate.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators Classical

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

private theorem moduli_weight_le_one
    {F : Type u} [Field F] [NumberField F] (v : NumberField.FinitePlace F) :
    Arithmetic.qPilotWeight v ≤ 1 := by
  have h := Arithmetic.qPilotWeight_sum_le_one_of_residueChar_filter
    ({v} : Finset (NumberField.FinitePlace F)) (Arithmetic.residueChar v)
    (Arithmetic.residueChar_prime v)
  have hf : ({v} : Finset (NumberField.FinitePlace F)).filter
      (fun w => Arithmetic.residueChar w = Arithmetic.residueChar v) = {v} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · exact And.left
    · intro hw
      subst w
      exact ⟨rfl, rfl⟩
  rw [hf, Finset.sum_singleton] at h
  exact h

/-- The moduli support and the actual selected q-root source have the same
representatives; this does not identify the selected base image with full support. -/
def iutInitialThetaModuliSelectedSourceEquiv
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    (iutInitialThetaOddModSupportFinset D) ≃
      {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
        s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D} := by
  let f := fun v : iutInitialThetaOddModSupportFinset D =>
    (⟨iutInitialThetaOddSupportSelectedQRootPlace D v.1
        ((iutInitialThetaOddModSupport_finite D).mem_toFinset.mp v.2),
      ⟨v.1, (iutInitialThetaOddModSupport_finite D).mem_toFinset.mp v.2, rfl⟩⟩ :
      {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
        s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D})
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro v w h
    apply Subtype.ext
    apply iutInitialThetaFinitePlaceSection_injective D
    exact congrArg (fun s => s.1.1) h
  · intro s
    rcases s.2 with ⟨v, hv, hplace⟩
    refine ⟨⟨v, (iutInitialThetaOddModSupport_finite D).mem_toFinset.mpr hv⟩, ?_⟩
    apply Subtype.ext
    exact Subtype.ext hplace

theorem iutInitialThetaModuliJLogTerm_eq_weightedBaseQOrder
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (hv : v ∈ iutInitialThetaOddModSupportFinset D) :
    let hv' := (iutInitialThetaOddModSupport_finite D).mem_toFinset.mp hv
    let R := iutInitialThetaOddSupportTorsionQRootSource D
    let B := iutInitialThetaOddSupportBaseQPilotSource D
    let s := iutInitialThetaOddSupportSelectedQRootPlace D v hv'
    let b := R.basePlace s
    Real.log ‖NumberField.FinitePlace.embedding v.maximalIdeal
      (⟨D.E.j, IntermediateField.mem_adjoin_simple_self ℚ D.E.j⟩ :
        ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))‖ /
      (2 * (D.prime.ℓ : ℝ) *
        (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ)) =
      (Arithmetic.qPilotWeight v / (Arithmetic.relRamIdx b.1 v : ℝ)) *
        ((B.qOrder b : ℝ) / (2 * (D.prime.ℓ : ℝ))) *
          Real.log (Arithmetic.residueChar b.1) := by
  let M := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)
  let hv' := (iutInitialThetaOddModSupport_finite D).mem_toFinset.mp hv
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let s := iutInitialThetaOddSupportSelectedQRootPlace D v hv'
  let b := R.basePlace s
  have hb : b.1 = iutInitialThetaSectionBasePlace D v :=
    iutInitialThetaOddSupportSelectedQRootPlace_basePlace_eq_sectionBasePlace D v hv'
  have hbv : Ideal.LiesOver b.1.maximalIdeal.asIdeal v.maximalIdeal.asIdeal := by
    rw [hb]
    exact iutInitialThetaSectionBasePlace_liesOver D v
  let j : M := ⟨D.E.j, IntermediateField.mem_adjoin_simple_self ℚ D.E.j⟩
  have hnorm := iutEmbedCompletion_norm_eq_pow hbv
    (NumberField.FinitePlace.embedding v.maximalIdeal j)
  rw [iutEmbedCompletion_embedding hbv j] at hnorm
  change ‖NumberField.FinitePlace.embedding b.1.maximalIdeal D.E.j‖ =
    ‖NumberField.FinitePlace.embedding v.maximalIdeal j‖ ^
      (Arithmetic.relRamIdx b.1 v * Arithmetic.relInertDeg b.1 v) at hnorm
  have hlog : Real.log ‖NumberField.FinitePlace.embedding b.1.maximalIdeal D.E.j‖ =
      ((Arithmetic.relRamIdx b.1 v : ℝ) * Arithmetic.relInertDeg b.1 v) *
        Real.log ‖NumberField.FinitePlace.embedding v.maximalIdeal j‖ := by
    rw [hnorm, Real.log_pow]
    push_cast
    ring
  have hbase := iutInitialThetaBaseQPilotLogTerm_eq_jLog D b
  unfold iutInitialThetaBaseQPilotLogTerm Arithmetic.qPilotWeight at hbase
  have hF : (Module.finrank ℚ D.F : ℝ) ≠ 0 := ne_of_gt Arithmetic.finrank_pos
  have hM : (Module.finrank ℚ M : ℝ) ≠ 0 := ne_of_gt Arithmetic.finrank_pos
  have hEll : (D.prime.ℓ : ℝ) ≠ 0 := by
    have h := D.prime.five_le
    positivity
  have he : (Arithmetic.relRamIdx b.1 v : ℝ) ≠ 0 := by
    exact_mod_cast Arithmetic.relRamIdx_ne_zero hbv
  have hi : (Arithmetic.inertDeg b.1 : ℝ) =
      (Arithmetic.inertDeg v : ℝ) * Arithmetic.relInertDeg b.1 v := by
    exact_mod_cast Arithmetic.inertDeg_eq_mul hbv
  have hf : (Arithmetic.relInertDeg b.1 v : ℝ) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hi
    exact (ne_of_gt (by exact_mod_cast Arithmetic.inertDeg_pos b.1 :
      (0 : ℝ) < Arithmetic.inertDeg b.1)) hi
  have hbaseLog : Real.log ‖NumberField.FinitePlace.embedding b.1.maximalIdeal D.E.j‖ =
      (Arithmetic.inertDeg b.1 : ℝ) * (B.qOrder b : ℝ) *
        Real.log (Arithmetic.residueChar b.1) := by
    field_simp [hF, hEll] at hbase
    nlinarith [hbase]
  have hmodLog : Real.log ‖NumberField.FinitePlace.embedding v.maximalIdeal j‖ =
      (Arithmetic.inertDeg v : ℝ) * (B.qOrder b : ℝ) *
        Real.log (Arithmetic.residueChar b.1) / Arithmetic.relRamIdx b.1 v := by
    rw [hbaseLog, hi] at hlog
    apply (eq_div_iff he).mpr
    apply mul_right_cancel₀ hf
    nlinarith [hlog]
  change Real.log ‖NumberField.FinitePlace.embedding v.maximalIdeal j‖ /
    (2 * (D.prime.ℓ : ℝ) * (Module.finrank ℚ M : ℝ)) = _
  rw [hmodLog]
  unfold Arithmetic.qPilotWeight
  ring

theorem iutInitialThetaModuliJLogTerm_le_selectedPaperTerm
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : iutInitialThetaOddModSupportFinset D) :
    let R := iutInitialThetaOddSupportTorsionQRootSource D
    let s := (iutInitialThetaModuliSelectedSourceEquiv D v).1
    Real.log ‖NumberField.FinitePlace.embedding v.1.maximalIdeal
      (⟨D.E.j, IntermediateField.mem_adjoin_simple_self ℚ D.E.j⟩ :
        ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))‖ /
      (2 * (D.prime.ℓ : ℝ) *
        (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ)) ≤
      ((Arithmetic.ramIdx s.1 : ℝ) * Arithmetic.ordp s.1 (R.qroot s)) *
        Real.log (Arithmetic.residueChar s.1) := by
  let hv := (iutInitialThetaOddModSupport_finite D).mem_toFinset.mp v.2
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let s := iutInitialThetaOddSupportSelectedQRootPlace D v.1 hv
  let b := R.basePlace s
  have hb : b.1 = iutInitialThetaSectionBasePlace D v.1 :=
    iutInitialThetaOddSupportSelectedQRootPlace_basePlace_eq_sectionBasePlace D v.1 hv
  have hbv : Ideal.LiesOver b.1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal := by
    rw [hb]
    exact iutInitialThetaSectionBasePlace_liesOver D v.1
  have he : (1 : ℝ) ≤ Arithmetic.relRamIdx b.1 v.1 := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Arithmetic.relRamIdx_ne_zero hbv)
  have hc : Arithmetic.qPilotWeight v.1 / (Arithmetic.relRamIdx b.1 v.1 : ℝ) ≤ 1 :=
    (div_le_one (lt_of_lt_of_le (by norm_num) he)).mpr
      ((moduli_weight_le_one v.1).trans he)
  have hOrd := iutInitialThetaOddSupportSelectedQRootPlace_ordp_eq_baseQOrder D v.1 hv
  change Arithmetic.ordp s.1 (R.qroot s) =
    (B.qOrder b : ℝ) / (2 * (D.prime.ℓ : ℝ) * Arithmetic.ramIdx b.1) at hOrd
  have hOrdPos : 0 ≤ Arithmetic.ordp s.1 (R.qroot s) := by
    rw [hOrd]
    positivity
  have hRam : (Arithmetic.ramIdx b.1 : ℝ) ≤ Arithmetic.ramIdx s.1 := by
    exact_mod_cast (by
      rw [Arithmetic.ramIdx_eq_mul (R.liesOver s)]
      exact Nat.le_mul_of_pos_right _
        (Nat.pos_of_ne_zero (Arithmetic.relRamIdx_ne_zero (R.liesOver s))) :
      Arithmetic.ramIdx b.1 ≤ Arithmetic.ramIdx s.1)
  have hterm : (B.qOrder b : ℝ) / (2 * (D.prime.ℓ : ℝ)) =
      (Arithmetic.ramIdx b.1 : ℝ) * Arithmetic.ordp s.1 (R.qroot s) := by
    rw [hOrd]
    have hr : (Arithmetic.ramIdx b.1 : ℝ) ≠ 0 := by
      exact_mod_cast (Arithmetic.ramIdx_pos b.1).ne'
    field_simp [hr]
  have hLog : 0 ≤ Real.log (Arithmetic.residueChar b.1) := by
    apply Real.log_nonneg
    exact_mod_cast (Arithmetic.residueChar_prime b.1).one_lt.le
  change _ ≤ ((Arithmetic.ramIdx s.1 : ℝ) * Arithmetic.ordp s.1 (R.qroot s)) *
    Real.log (Arithmetic.residueChar s.1)
  rw [iutInitialThetaModuliJLogTerm_eq_weightedBaseQOrder D v.1 v.2]
  change (Arithmetic.qPilotWeight v.1 / (Arithmetic.relRamIdx b.1 v.1 : ℝ)) *
    ((B.qOrder b : ℝ) / (2 * (D.prime.ℓ : ℝ))) * Real.log (Arithmetic.residueChar b.1) ≤ _
  rw [hterm, Arithmetic.residueChar_eq_of_liesOver (R.liesOver s)]
  apply mul_le_mul_of_nonneg_right _ hLog
  calc
    _ ≤ 1 * ((Arithmetic.ramIdx b.1 : ℝ) * Arithmetic.ordp s.1 (R.qroot s)) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg (Nat.cast_nonneg _) hOrdPos)
    _ ≤ _ := by
      rw [one_mul]
      exact mul_le_mul_of_nonneg_right hRam hOrdPos

theorem iutInitialThetaFullBaseQPilotLogSum_le_selectedPaperSum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    iutInitialThetaFullBaseQPilotLogSum D ≤ iutInitialThetaSelectedQRootPaperSum D := by
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let S := {s : R.badFinset // s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
  letI : Fintype S := (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
  let e := iutInitialThetaModuliSelectedSourceEquiv D
  let term : S → ℝ := fun s => ((Arithmetic.ramIdx s.1.1 : ℝ) *
    Arithmetic.ordp s.1.1 (R.qroot s.1)) * Real.log (Arithmetic.residueChar s.1.1)
  rw [iutInitialThetaFullBaseQPilotLogSum_eq_moduliJLogSum, Finset.sum_div]
  calc
    _ = ∑ v : iutInitialThetaOddModSupportFinset D,
        Real.log ‖NumberField.FinitePlace.embedding v.1.maximalIdeal
          (⟨D.E.j, IntermediateField.mem_adjoin_simple_self ℚ D.E.j⟩ :
            ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))‖ /
          (2 * (D.prime.ℓ : ℝ) *
            (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ)) := by
      exact (Finset.sum_coe_sort _ _).symm
    _ ≤ ∑ v : iutInitialThetaOddModSupportFinset D, term (e v) := by
      exact Finset.sum_le_sum fun v _ => iutInitialThetaModuliJLogTerm_le_selectedPaperTerm D v
    _ = ∑ s : S, term s := e.sum_comp term
    _ = _ := rfl

theorem iutInitialThetaFullBaseQPilotLogSum_le_representativeSum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    iutInitialThetaFullBaseQPilotLogSum D ≤
      ∑ w : (iutInitialThetaOddTateSectionTateParameterData D).places,
        iutInitialThetaSectionRepresentativeTerm D w.1 := by
  rw [← iutInitialThetaSelectedQRootPaperSum_eq_representativeSum]
  exact iutInitialThetaFullBaseQPilotLogSum_le_selectedPaperSum D

end
end JoshiTeich.Act1Scene1
