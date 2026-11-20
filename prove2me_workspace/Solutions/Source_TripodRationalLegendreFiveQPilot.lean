import Solutions.Source_TripodRationalLegendreFivePlace
import Solutions.Source_TripodRationalLegendreFiveTransport
import Solutions.Source_ReferenceIutCor312QPilotModuli
import Solutions.Source_TripodTowerStepIII
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_GoodReductionHeight
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField IsDedekindDomain
open scoped BigOperators Classical

private theorem liesOver_rationalFivePlace_iff {K : Type*} [Field K] [NumberField K]
    (w : FinitePlace K) :
    FinitePlace.LiesOver w rationalFivePlace ↔ residueChar w = 5 := by
  refine ⟨fun hw => (residueChar_eq_of_liesOver hw).trans residueChar_rationalFivePlace, ?_⟩
  intro hp
  let v := placeUnder (k := ℚ) w
  have hwv : FinitePlace.LiesOver w v := liesOver_placeUnder w
  have hchar : residueChar v = residueChar rationalFivePlace :=
    (residueChar_eq_of_liesOver hwv).symm.trans (hp.trans residueChar_rationalFivePlace.symm)
  have heq : v = rationalFivePlace := by
    apply FinitePlace.maximalIdeal_injective
    apply HeightOneSpectrum.ext
    apply Ideal.comap_injective_of_surjective (algebraMap ℤ (𝓞 ℚ))
      (Rat.int_algebraMap_surjective (𝓞 ℚ))
    change v.maximalIdeal.asIdeal.under ℤ = rationalFivePlace.maximalIdeal.asIdeal.under ℤ
    rw [under_int_eq, under_int_eq, hchar]
  exact heq ▸ hwv

private theorem div_sum_rationalLegendreFive_log {K : Type*} [Field K] [NumberField K]
    (m : ℕ) (hm : 0 < m) {j : K}
    (hj : j = algebraMap ℚ K (legendreJ (rationalLegendreFiveParam m)))
    (S : Finset (FinitePlace K)) (hS : ∀ w, w ∈ S ↔ residueChar w = 5) :
    (∑ w ∈ S, Real.log (w j)) / (Module.finrank ℚ K : ℝ) = 2 * (m : ℝ) * Real.log 5 := by
  have hspec (w : FinitePlace K) : w ∈ S ↔ FinitePlace.LiesOver w rationalFivePlace :=
    (hS w).trans (liesOver_rationalFivePlace_iff w).symm
  have hlog (w : FinitePlace K) (hw : w ∈ S) :
      Real.log (w j) = (relLocalDeg w rationalFivePlace : ℝ) * (2 * (m : ℝ) * Real.log 5) := by
    rw [hj, apply_algebraMap_eq_pow ((hspec w).mp hw), rationalFivePlace_legendreJ m hm]
    simp only [Real.log_pow, Nat.cast_mul, Nat.cast_ofNat]
  rw [Finset.sum_congr rfl hlog, ← Finset.sum_mul, ← Nat.cast_sum,
    sum_relLocalDeg_liesOver rationalFivePlace S hspec]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast (Module.finrank_pos :
    0 < Module.finrank ℚ K).ne')

section Provider

variable (P : CurveProviders) (m : ℕ) (hm : 0 < m)

include hm in
/-- The norm of the provider's invariant at each curve place over 5. -/
theorem norm_j_rationalLegendreFivePoint
    {w : FinitePlace (P.curve (rationalLegendreFivePoint m)).F}
    (hw : FinitePlace.LiesOver w rationalFivePlace) :
    w (P.curve (rationalLegendreFivePoint m)).E.j =
      (5 : ℝ) ^ ((2 * m) * relLocalDeg w rationalFivePlace) := by
  rw [curve_j_rationalLegendreFivePoint P m, apply_algebraMap_eq_pow hw,
    rationalFivePlace_legendreJ m hm, ← pow_mul]

include hm in
/-- Every curve place of residue characteristic 5 is multiplicative. -/
theorem mem_badAll_rationalLegendreFivePoint
    (w : FinitePlace (P.curve (rationalLegendreFivePoint m)).F) (hw : residueChar w = 5) :
    w ∈ (P.curve (rationalLegendreFivePoint m)).badAll := by
  let x := rationalLegendreFivePoint m
  let C := P.curve x
  have hover := (liesOver_rationalFivePlace_iff w).mpr hw
  have hnorm : 1 < w C.E.j := by
    rw [norm_j_rationalLegendreFivePoint P m hm hover]
    exact one_lt_pow₀ (by norm_num)
      (Nat.mul_ne_zero (Nat.mul_ne_zero (by decide) hm.ne') (relLocalDeg_ne_zero hover))
  change HasMultiplicativeReductionAt C.E w
  apply (hasMultiplicativeReductionAt_iff_of_stable C.E w
    ((P.arith x).stable_reduction w)).mpr
  intro hval
  apply (not_le.mpr hnorm)
  rw [← FinitePlace.norm_embedding_eq]
  exact (norm_emb_le_one_iff _).mpr hval

include hm in
/-- Every moduli place of residue characteristic 5 belongs to the selected support. -/
theorem mem_VBadOf_rationalLegendreFivePoint {ℓ : ℕ} (h7 : 7 ≤ ℓ)
    (v : FinitePlace ↥(fieldOfModuli (P.curve (rationalLegendreFivePoint m)).F
      (P.curve (rationalLegendreFivePoint m)).E)) (hv : residueChar v = 5) :
    v ∈ (P.curve (rationalLegendreFivePoint m)).VBadOf ℓ := by
  let C := P.curve (rationalLegendreFivePoint m)
  refine ⟨?_, ?_, JoshiTeich.ReferenceIut.FinitePlace.exists_liesOver (K := C.F) v, ?_⟩
  · change residueChar v ≠ 2
    omega
  · change residueChar v ≠ ℓ
    omega
  · intro w hwv
    exact mem_badAll_rationalLegendreFivePoint P m hm w
      ((residueChar_eq_of_liesOver hwv).trans hv)

include hm in
/-- A place over 5 supplies the (P5) witness for this curve and prime. -/
theorem rationalLegendreFivePoint_p5 {ℓ : ℕ} (h7 : 7 ≤ ℓ) :
    ∃ w ∈ (P.curve (rationalLegendreFivePoint m)).badAll,
      AbcAdaptation.Reference.Iut.residueChar w ≠ 2 ∧
      AbcAdaptation.Reference.Iut.residueChar w ≠ ℓ := by
  obtain ⟨w, hw⟩ := JoshiTeich.ReferenceIut.FinitePlace.exists_liesOver
    (K := (P.curve (rationalLegendreFivePoint m)).F) rationalFivePlace
  have hchar := (liesOver_rationalFivePlace_iff w).mp hw
  refine ⟨w, mem_badAll_rationalLegendreFivePoint P m hm w hchar, ?_, ?_⟩
  · change residueChar w ≠ 2
    omega
  · change residueChar w ≠ ℓ
    omega

variable {AG : AnabelianGeometry.{0}} {TG : TemperedGeometry AG}

/-- The complete fibers at 5 give the same normalized log contribution in the moduli
field and in the curve field used for the q-pilot. -/
theorem rationalLegendreFivePoint_qPilot {ℓ : ℕ} (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
    (hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ),
      A.toGL ∈ (P.modRep (rationalLegendreFivePoint m) ℓ hℓ).rep.range)
    (hP2 : ∀ w (hw : w ∈ (P.curve (rationalLegendreFivePoint m)).badAll),
      ¬ ℓ ∣ (P.tate (rationalLegendreFivePoint m)).qOrder w hw)
    (anab : AnabelianExistence AG TG)
    (hcore : OrbicurveDataSection.HasCoreUniversally AG
      (P.curve (rationalLegendreFivePoint m)).F (P.curve (rationalLegendreFivePoint m)).E) :
    let x := rationalLegendreFivePoint m
    let hP5 := rationalLegendreFivePoint_p5 P m hm h7
    let D := thetaDataOf P x hℓ h7 hsl hP2 hP5 anab hcore
    let QI := qPilotInputsOf P x hℓ h7 hsl hP2 hP5 anab hcore
    (∑ v ∈ QI.badModuliFinset.filter (fun v => residueChar v = 5), Real.log (v D.moduliJ)) /
        (Module.finrank ℚ ↥(fieldOfModuli D.F D.E) : ℝ) = 2 * (m : ℝ) * Real.log 5 ∧
    (∑ w ∈ QI.qPilot.badFinset.attach.filter (fun w => residueChar w.1 = 5),
        QI.qPilot.weight w.1 * (D.prime.qOrder w.1 (QI.qPilot.mem_bad w.2) : ℝ) *
          Real.log (AbcAdaptation.Reference.Iut.residueChar w.1)) = 2 * (m : ℝ) * Real.log 5 ∧
    QI.qPilot.lhs ≤ -((m : ℝ) * Real.log 5 / (ℓ : ℝ)) := by
  intro x hP5 D QI
  let j := legendreJ (rationalLegendreFiveParam m)
  have hj : D.E.j = algebraMap ℚ D.F j := curve_j_rationalLegendreFivePoint P m
  have hjM : D.moduliJ = algebraMap ℚ ↥(fieldOfModuli D.F D.E) j := by
    apply (algebraMap ↥(fieldOfModuli D.F D.E) D.F).injective
    change D.E.j = algebraMap ↥(fieldOfModuli D.F D.E) D.F
      (algebraMap ℚ ↥(fieldOfModuli D.F D.E) j)
    rw [← IsScalarTower.algebraMap_apply]
    exact hj
  have hmoduli (v : FinitePlace ↥(fieldOfModuli D.F D.E)) :
      v ∈ QI.badModuliFinset.filter (fun v => residueChar v = 5) ↔ residueChar v = 5 := by
    rw [Finset.mem_filter, QI.mem_badModuliFinset]
    exact ⟨And.right, fun hv => ⟨mem_VBadOf_rationalLegendreFivePoint P m hm h7 v hv, hv⟩⟩
  refine ⟨div_sum_rationalLegendreFive_log m hm hjM _ hmoduli, ?_⟩
  have hcurve (w : FinitePlace D.F) :
      w ∈ QI.qPilot.badFinset.filter (fun w => residueChar w = 5) ↔ residueChar w = 5 := by
    rw [Finset.mem_filter]
    refine ⟨And.right, fun hw => ⟨(Set.ext_iff.mp QI.qPilot.badFinset_spec w).mpr ?_, hw⟩⟩
    let v : FinitePlace ↥(fieldOfModuli D.F D.E) := placeUnder w
    have hwv : FinitePlace.LiesOver w v := liesOver_placeUnder w
    exact ⟨v, mem_VBadOf_rationalLegendreFivePoint P m hm h7 v
      ((residueChar_eq_of_liesOver hwv).symm.trans hw), hwv⟩
  let contribution (w : {w // w ∈ QI.qPilot.badFinset}) : ℝ :=
    QI.qPilot.weight w.1 * (D.prime.qOrder w.1 (QI.qPilot.mem_bad w.2) : ℝ) *
      Real.log (AbcAdaptation.Reference.Iut.residueChar w.1)
  have hfive : (∑ w ∈ QI.qPilot.badFinset.attach.filter (fun w => residueChar w.1 = 5),
      contribution w) = 2 * (m : ℝ) * Real.log 5 := by
    calc
      _ = ∑ w ∈ QI.qPilot.badFinset.attach.filter (fun w => residueChar w.1 = 5),
          Real.log (w.1 D.E.j) / (Module.finrank ℚ D.F : ℝ) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        change ((AbcAdaptation.Reference.Iut.inertDeg D.F w.1 : ℝ) / Module.finrank ℚ D.F) *
          (D.prime.qOrder w.1 (QI.qPilot.mem_bad w.2) : ℝ) *
          Real.log (AbcAdaptation.Reference.Iut.residueChar w.1) =
            Real.log (w.1 D.E.j) / Module.finrank ℚ D.F
        rw [D.log_j_eq_qOrder w.1 (QI.qPilot.mem_bad w.2)]
        ring
      _ = (∑ w ∈ QI.qPilot.badFinset.filter (fun w => residueChar w = 5), Real.log (w D.E.j)) /
          (Module.finrank ℚ D.F : ℝ) := by
        rw [Finset.sum_div]
        simpa only [Finset.sum_filter] using Finset.sum_attach QI.qPilot.badFinset
          (fun w => if residueChar w = 5 then Real.log (w D.E.j) / (Module.finrank ℚ D.F : ℝ) else 0)
      _ = _ := div_sum_rationalLegendreFive_log m hm hj _ hcurve
  refine ⟨hfive, ?_⟩
  have hsum : 2 * (m : ℝ) * Real.log 5 ≤ QI.qPilot.logQ := by
    rw [← hfive]
    change _ ≤ ∑ w ∈ QI.qPilot.badFinset.attach, contribution w
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun w _ _ =>
      mul_nonneg (mul_nonneg (QI.qPilot.weight_pos w.1 w.2).le (Nat.cast_nonneg _))
        (Real.log_natCast_nonneg _))
  change -(QI.qPilot.logQ / (2 * (ℓ : ℝ))) ≤ _
  have hle := div_le_div_of_nonneg_right hsum
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg ℓ))
  rw [mul_assoc, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)] at hle
  exact neg_le_neg hle

end Provider

end AbcAdaptation.Tripod
