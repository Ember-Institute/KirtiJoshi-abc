import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOrdinaryLogHullVolume

/-!
source-id: JT-SCENE1-ACTUAL-ORDINARY-LOG-COLLATION
source: actual ordinary Kummer-log witness, singleton normalization hull
and relative/residue weighted volume; Joshi III 3520--3574, 3624--3631.
fidelity: a collation containing the ordinary witness has positive finite
Haar hulls and a lower bound with the explicit pStar correction retained.
Its negative-log bound includes that correction cost.
boundary: Scene1/Derived; no paper theta/BK/untilt identity is assumed.
-/

namespace JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (n : ℕ)
local instance ordinaryCollationPrime (v : iutInitialThetaOddModSupportFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩

theorem degreeCorrection_eq_one_pow (v : iutInitialThetaOddModSupportFinset D) :
    degreeCorrection D n v = degreeCorrection D 1 v ^ n := by
  let s := FullSupportPaperWeightedHull.selected D v
  let c : ℝ := ‖(LocalPadicLog.paperScale (Arithmetic.residueChar s.1) : PrincipalUnitKummer.localField D s)‖ ^
    (1 / (Arithmetic.localDeg s.1 : ℝ))
  have hc (m : ℕ) : degreeCorrection D m v = c ^ m := by
    change (∏ _ : Fin m, c) = c ^ m
    exact Fin.prod_const m c
  rw [hc n, hc 1, pow_one]

theorem localCorrection_eq_one_pow (v : iutInitialThetaOddModSupportFinset D) :
    localCorrection D n v = localCorrection D 1 v ^ n := by
  rw [localCorrection, degreeCorrection_eq_one_pow D n v, pow_right_comm,
    ← Real.rpow_pow_comm (pow_nonneg (degreeCorrection_pos D 1 v).le _)]
  rfl

theorem correction_eq_one_pow : correction D n = correction D 1 ^ n := by
  simp only [correction, localCorrection_eq_one_pow D n, Finset.prod_pow]

theorem correctionCost_nonneg : 0 ≤ -Real.log (correction D 1) :=
  neg_nonneg.mpr (Real.log_nonpos (correction_pos D 1).le (correction_le_one D 1))

theorem negLog_volume_eq_mul_correctedCost :
    -Real.log (volume D n) = (n : ℝ) *
      (FullSupportPaperWeightedHull.weightedPaperSum D - Real.log (correction D 1)) := by
  rw [negLog_volume_eq_weightedSum_add_correction, correction_eq_one_pow, Real.log_pow]
  ring

variable {κ : Type*}
variable (C : ∀ v : iutInitialThetaOddModSupportFinset D, κ → Set (packet D n v).Tensor)
variable (hw : ∀ v, witness D n v ∈ ⋃ k, C v k)
variable (hunit : ∀ v k, C v k ⊆ (packet D n v).normalization)

include hw in
theorem ordinary_region_subset_collation (v : iutInitialThetaOddModSupportFinset D) :
    (region D n v : Set (packet D n v).Tensor) ⊆ FullSupportWitnessHull.region D n C v :=
  Submodule.span_mono (Set.singleton_subset_iff.mpr (hw v))

include hw hunit in
theorem ordinary_collation_haar_pos_lt_top (v : iutInitialThetaOddModSupportFinset D) :
    0 < (packet D n v).normalizationHaar (FullSupportWitnessHull.region D n C v) ∧
      (packet D n v).normalizationHaar (FullSupportWitnessHull.region D n C v) < ⊤ :=
  (packet D n v).normalizationHull_haar_pos_lt_top_of_pure_mem
    (⋃ k, C v k) (fun i => scalar D (FullSupportThetaLogHull.sourceAt D n v i))
    (fun i => scalar_ne_zero D _) (hw v) (Set.iUnion_subset (hunit v))

include hw hunit in
theorem ordinary_localVolume_le_collation (v : iutInitialThetaOddModSupportFinset D) :
    localVolume D n v ≤ FullSupportWitnessHull.localVolume D n C v := by
  have hv := (packet D n v).normalizationDegreeVolume_mono
    (ordinary_region_subset_collation D n C hw v) (ordinary_collation_haar_pos_lt_top D n C hw hunit v).2.ne
  have h0 : 0 ≤ (packet D n v).normalizationDegreeVolume (region D n v) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  exact Real.rpow_le_rpow (pow_nonneg h0 _)
    (pow_le_pow_left₀ h0 hv (Arithmetic.localDeg v.1)) (by positivity)

include hw hunit in
theorem ordinary_volume_le_collation : volume D n ≤ FullSupportWitnessHull.volume D n C := by
  apply Finset.prod_le_prod
    (fun v _ => Real.rpow_nonneg (pow_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _) _) _)
  exact fun v _ => ordinary_localVolume_le_collation D n C hw hunit v

include hw hunit in
theorem corrected_rootProduct_pow_le_collation :
    correction D n * actualSelectedPaperRootNormProduct D ^ n ≤ FullSupportWitnessHull.volume D n C := by
  apply le_trans _ (ordinary_volume_le_collation D n C hw hunit)
  rw [volume_eq_corrected]
  exact mul_le_mul_of_nonneg_left
    (FullSupportPaperWeightedHull.selectedPaperRootProduct_pow_le_volume D n) (correction_pos D n).le

include hw hunit in
theorem ordinary_collation_volume_pos : 0 < FullSupportWitnessHull.volume D n C :=
  (volume_pos D n).trans_le (ordinary_volume_le_collation D n C hw hunit)

include hw hunit in
theorem ordinary_collation_negLog_le_corrected :
    -Real.log (FullSupportWitnessHull.volume D n C) ≤
      (n : ℝ) * FullSupportPaperWeightedHull.weightedPaperSum D - Real.log (correction D n) := by
  rw [← negLog_volume_eq_weightedSum_add_correction D n]
  exact neg_le_neg (Real.log_le_log (volume_pos D n) (ordinary_volume_le_collation D n C hw hunit))

include hw hunit in
theorem ordinary_collation_absLog_le_corrected :
    |Real.log (FullSupportWitnessHull.volume D n C)| ≤
      (n : ℝ) * FullSupportPaperWeightedHull.weightedPaperSum D - Real.log (correction D n) := by
  rw [abs_of_nonpos (Real.log_nonpos (ordinary_collation_volume_pos D n C hw hunit).le
    (FullSupportWitnessHull.volume_le_one D n C hunit))]
  exact ordinary_collation_negLog_le_corrected D n C hw hunit

include hw hunit in
theorem ordinary_collation_averageAbsLog_le_correctedCost (hn : 0 < n) :
    (1 / (n : ℝ)) * |Real.log (FullSupportWitnessHull.volume D n C)| ≤
      FullSupportPaperWeightedHull.weightedPaperSum D - Real.log (correction D 1) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h := ordinary_collation_absLog_le_corrected D n C hw hunit
  rw [correction_eq_one_pow, Real.log_pow, ← mul_sub] at h
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 1 / (n : ℝ) by positivity)
  simpa only [← mul_assoc, one_div_mul_cancel hn', one_mul] using hm

end
end JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
