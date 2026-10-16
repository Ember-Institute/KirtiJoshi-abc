import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOrdinaryLogGlobalMargin

/-!
source-id: JT-SCENE1-ACTUAL-ORDINARY-LOG-SINGLETON-CRITERION
source: actual ordinary-log pure witnesses, singleton normalization hulls
and their exact Haar volume; Joshi III 3520--3574, 3624--3631.
fidelity: constructs a legal actual singleton collation. For positive
length its average absolute log equals the corrected cost, so its paper
bound holds iff the total arithmetic margin is nonnegative. The same
criterion characterizes a bound for every collation with these two laws.
boundary: Scene1/Derived; no actual margin sign or paper/BK/untilt identity.
-/

namespace JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (n : ℕ)
local instance singletonOrdinaryPrime (v : iutInitialThetaOddModSupportFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩

theorem ordinary_witness_mem_normalization (v : iutInitialThetaOddModSupportFinset D) :
    witness D n v ∈ (packet D n v).normalization := by
  apply (packet D n v).unitLattice_le_normalization
  exact (packet D n v).pure_mem_lattice _ _ (fun i => by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (norm_scalar_lt_one D (FullSupportThetaLogHull.sourceAt D n v i)).le)

def ordinarySingletonCollation (v : iutInitialThetaOddModSupportFinset D) (_ : Unit) :
    Set (packet D n v).Tensor := {witness D n v}

theorem ordinarySingletonCollation_laws :
    (∀ v, witness D n v ∈ ⋃ k, ordinarySingletonCollation D n v k) ∧
      (∀ v k, ordinarySingletonCollation D n v k ⊆ (packet D n v).normalization) := by
  constructor
  · intro v
    simp only [ordinarySingletonCollation, Set.iUnion_const, Set.mem_singleton_iff]
  · intro v _
    exact Set.singleton_subset_iff.mpr (ordinary_witness_mem_normalization D n v)

theorem ordinarySingletonCollation_region_eq (v : iutInitialThetaOddModSupportFinset D) :
    FullSupportWitnessHull.region D n (ordinarySingletonCollation D n) v = region D n v := by
  simp only [FullSupportWitnessHull.region, ordinarySingletonCollation, Set.iUnion_const, region]

theorem ordinarySingletonCollation_volume_eq :
    FullSupportWitnessHull.volume D n (ordinarySingletonCollation D n) = volume D n := by
  unfold FullSupportWitnessHull.volume volume
  apply Finset.prod_congr rfl
  intro v _
  unfold FullSupportWitnessHull.localVolume
  rw [ordinarySingletonCollation_region_eq]
  rfl

theorem ordinary_volume_le_one : volume D n ≤ 1 :=
  (volume_le_normalized D n).trans (FullSupportPaperWeightedHull.volume_le_one D n)

theorem ordinary_averageAbsLog_eq_correctedCost (hn : 0 < n) :
    (1 / (n : ℝ)) * |Real.log (volume D n)| =
      FullSupportPaperWeightedHull.weightedPaperSum D - Real.log (correction D 1) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [abs_of_nonpos (Real.log_nonpos (volume_pos D n).le (ordinary_volume_le_one D n)),
    negLog_volume_eq_mul_correctedCost, ← mul_assoc, one_div_mul_cancel hn', one_mul]

theorem ordinarySingletonCollation_bound_iff_global_margin (hn : 0 < n) :
    ((1 / (n : ℝ)) * |Real.log (FullSupportWitnessHull.volume D n (ordinarySingletonCollation D n))| ≤
      iutInitialThetaSelectedQRootPaperSum D) ↔ 0 ≤ globalArithmeticMargin D := by
  rw [ordinarySingletonCollation_volume_eq, ordinary_averageAbsLog_eq_correctedCost D n hn]
  exact (globalArithmeticMargin_nonneg_iff D).symm

/-- Quantifies collations on the existing block; it does not quantify paper theta loci. -/
theorem all_ordinary_collations_bound_iff_global_margin (hn : 0 < n) :
    (∀ (C : ∀ v : iutInitialThetaOddModSupportFinset D, Unit → Set (packet D n v).Tensor),
      (∀ v, witness D n v ∈ ⋃ k, C v k) →
      (∀ v k, C v k ⊆ (packet D n v).normalization) →
      (1 / (n : ℝ)) * |Real.log (FullSupportWitnessHull.volume D n C)| ≤
        iutInitialThetaSelectedQRootPaperSum D) ↔ 0 ≤ globalArithmeticMargin D := by
  constructor
  · intro h
    exact (ordinarySingletonCollation_bound_iff_global_margin D n hn).mp
      (h (ordinarySingletonCollation D n) (ordinarySingletonCollation_laws D n).1
        (ordinarySingletonCollation_laws D n).2)
  · intro h C hw hunit
    exact ordinary_collation_averageAbsLog_le_paperSum_of_global_margin D n C hw hunit hn h

theorem ordinarySingletonCollation_violates_bound_of_negative_margin
    (hn : 0 < n) (h : globalArithmeticMargin D < 0) :
    iutInitialThetaSelectedQRootPaperSum D <
      (1 / (n : ℝ)) * |Real.log (FullSupportWitnessHull.volume D n (ordinarySingletonCollation D n))| := by
  apply lt_of_not_ge
  intro hb
  exact (not_le_of_gt h) ((ordinarySingletonCollation_bound_iff_global_margin D n hn).mp hb)

end
end JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
