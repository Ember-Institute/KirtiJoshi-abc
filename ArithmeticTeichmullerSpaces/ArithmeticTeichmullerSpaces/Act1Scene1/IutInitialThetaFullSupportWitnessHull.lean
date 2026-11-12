import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorWitnessHull
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFullSupportPaperWeightedVolume

/-!
source-id: JT-SCENE1-INITIAL-THETA-FULL-SUPPORT-WITNESS-HULL
source: Joshi III standard-point class and principal hull estimate
(3624--3631), with actual complete section ordinary-log witnesses.
fidelity: one actual log tensor per moduli block, contained in a collation,
gives compact positive-Haar hulls and the complete corrected relative-weight
volume bound. No whole scalar-generator family is an input. Witness
membership and upper containment are geometric obligations; theta/BK/untilt
identification, mixed-moduli descent and source sign remain open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.FullSupportWitnessHull
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section

private def correctedVolume
    {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {ι : Type} [Fintype ι] (P : LocalCompletion.Packet K p ι)
    (d f : ℕ) (U : Set P.Tensor) : ℝ :=
  (P.normalizationDegreeVolume U ^ d) ^ (1 / (f : ℝ))

private theorem correctedVolume_nonneg
    {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {ι : Type} [Fintype ι] (P : LocalCompletion.Packet K p ι)
    (d f : ℕ) (U : Set P.Tensor) : 0 ≤ correctedVolume P d f U :=
  Real.rpow_nonneg (pow_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _) _) _

private theorem correctedVolume_mono
    {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {ι : Type} [Fintype ι] (P : LocalCompletion.Packet K p ι)
    (d f : ℕ) {U V : Set P.Tensor} (hUV : U ⊆ V) (hV : P.normalizationHaar V ≠ ⊤) :
    correctedVolume P d f U ≤ correctedVolume P d f V := by
  apply Real.rpow_le_rpow (pow_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _) _) _
    (by positivity)
  exact pow_le_pow_left₀ (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    (P.normalizationDegreeVolume_mono hUV hV) d

private theorem correctedVolume_le_one
    {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {ι : Type} [Fintype ι] (P : LocalCompletion.Packet K p ι)
    (d f : ℕ) (U : Set P.Tensor) (hU : U ⊆ P.normalization) :
    correctedVolume P d f U ≤ 1 := by
  apply Real.rpow_le_one (pow_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _) _) _
    (by positivity)
  exact pow_le_one₀ (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    (P.normalizationDegreeVolume_le_one U hU)

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (n : ℕ)

abbrev packet (v : iutInitialThetaOddModSupportFinset D) := FullSupportThetaLogHull.packet D n v

local instance witnessPrime (v : iutInitialThetaOddModSupportFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩

def witness (v : iutInitialThetaOddModSupportFinset D) : (packet D n v).Tensor :=
  (packet D n v).pure
    (fun i => iutInitialThetaFullQRootLogValue D (FullSupportThetaLogHull.sourceAt D n v i))

private theorem scalar_ne_zero (v : iutInitialThetaOddModSupportFinset D) (i : Fin n) :
    iutInitialThetaFullQRootLogValue D (FullSupportThetaLogHull.sourceAt D n v i) ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [iutInitialThetaFullQRootLogValue_norm_eq]
  exact norm_ne_zero_iff.mpr ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero _)

theorem witness_isUnit (v : iutInitialThetaOddModSupportFinset D) :
    IsUnit (witness D n v) :=
  (packet D n v).pure_isUnit _ (scalar_ne_zero D n v)

theorem witness_mem_base_region (v : iutInitialThetaOddModSupportFinset D) :
    witness D n v ∈ FullSupportThetaLogHull.region D n v := by
  change witness D n v ∈ (FullSupportThetaLogHull.region D n v : Set (packet D n v).Tensor)
  rw [FullSupportThetaLogHull.region_eq_scalarNormalization]
  change witness D n v ∈ ((packet D n v).scalarNormalization _ _ : Set (packet D n v).Tensor)
  rw [(packet D n v).scalarNormalization_eq_principalRegion]
  exact ⟨1, (packet D n v).normalization.one_mem, mul_one _⟩

def singletonCollation (v : iutInitialThetaOddModSupportFinset D) (_ : Unit) :
    Set (packet D n v).Tensor := {witness D n v}

theorem singletonCollation_laws :
    (∀ v, witness D n v ∈ ⋃ k, singletonCollation D n v k) ∧
      (∀ v k, singletonCollation D n v k ⊆ (packet D n v).normalization) := by
  constructor
  · intro v
    simp [singletonCollation]
  · intro v _
    exact Set.singleton_subset_iff.mpr
      (FullSupportThetaLogHull.region_subset_normalization D n v (witness_mem_base_region D n v))

variable {κ : Type*}
variable (C : ∀ v : iutInitialThetaOddModSupportFinset D, κ → Set (packet D n v).Tensor)

def region (v : iutInitialThetaOddModSupportFinset D) :
    Submodule (packet D n v).normalization (packet D n v).Tensor :=
  (packet D n v).normalizationHull (⋃ k, C v k)

def localVolume (v : iutInitialThetaOddModSupportFinset D) : ℝ :=
  correctedVolume (packet D n v) (Arithmetic.localDeg v.1)
    (Arithmetic.inertDeg (FullSupportPaperWeightedHull.selected D v).1) (region D n C v)

def volume : ℝ := ∏ v : iutInitialThetaOddModSupportFinset D, localVolume D n C v

theorem singleton_region_eq_base (v : iutInitialThetaOddModSupportFinset D) :
    (region D n (singletonCollation D n) v : Set (packet D n v).Tensor) =
      (FullSupportThetaLogHull.region D n v : Set (packet D n v).Tensor) := by
  have hU : (⋃ k, singletonCollation D n v k) = {witness D n v} := by
    simp [singletonCollation]
  rw [region, hU, (packet D n v).normalizationHull_singleton_eq_principalRegion,
    FullSupportThetaLogHull.region_eq_scalarNormalization]
  exact ((packet D n v).scalarNormalization_eq_principalRegion _ _).symm

theorem singleton_volume_eq_base :
    volume D n (singletonCollation D n) = FullSupportPaperWeightedHull.volume D n := by
  unfold volume FullSupportPaperWeightedHull.volume
  apply Finset.prod_congr rfl
  intro v _
  unfold localVolume
  rw [singleton_region_eq_base]
  rfl

variable (hw : ∀ v, witness D n v ∈ ⋃ k, C v k)
variable (hunit : ∀ v k, C v k ⊆ (packet D n v).normalization)

include hw in
theorem base_region_subset_region (v : iutInitialThetaOddModSupportFinset D) :
    (FullSupportThetaLogHull.region D n v : Set (packet D n v).Tensor) ⊆ region D n C v := by
  rw [FullSupportThetaLogHull.region_eq_scalarNormalization]
  exact (packet D n v).scalarNormalization_subset_normalizationHull_of_pure_mem
    (⋃ k, C v k) _ (scalar_ne_zero D n v) (hw v)

include hw hunit in
theorem region_isCompact (v : iutInitialThetaOddModSupportFinset D) :
    IsCompact (region D n C v : Set (packet D n v).Tensor) :=
  (packet D n v).normalizationHull_isCompact_of_pure_mem _ _ (scalar_ne_zero D n v)
    (hw v) (Set.iUnion_subset (hunit v))

include hw hunit in
theorem region_haar_pos_lt_top (v : iutInitialThetaOddModSupportFinset D) :
    0 < (packet D n v).normalizationHaar (region D n C v) ∧
      (packet D n v).normalizationHaar (region D n C v) < ⊤ :=
  (packet D n v).normalizationHull_haar_pos_lt_top_of_pure_mem _ _ (scalar_ne_zero D n v)
    (hw v) (Set.iUnion_subset (hunit v))

include hw hunit in
theorem base_localVolume_le (v : iutInitialThetaOddModSupportFinset D) :
    FullSupportPaperWeightedHull.localVolume D n v ≤ localVolume D n C v := by
  change correctedVolume (packet D n v) (Arithmetic.localDeg v.1)
    (Arithmetic.inertDeg (FullSupportPaperWeightedHull.selected D v).1)
    (FullSupportThetaLogHull.region D n v) ≤ _
  exact correctedVolume_mono (packet D n v) _ _
    (base_region_subset_region D n C hw v) (region_haar_pos_lt_top D n C hw hunit v).2.ne

include hw hunit in
theorem base_volume_le : FullSupportPaperWeightedHull.volume D n ≤ volume D n C := by
  exact Finset.prod_le_prod
    (fun v _ => correctedVolume_nonneg (packet D n v) _ _ (FullSupportThetaLogHull.region D n v))
    (fun v _ => base_localVolume_le D n C hw hunit v)

include hw hunit in
theorem volume_pos : 0 < volume D n C :=
  (FullSupportPaperWeightedHull.volume_pos D n).trans_le (base_volume_le D n C hw hunit)

include hunit in
theorem volume_le_one : volume D n C ≤ 1 := by
  apply Finset.prod_le_one
    (fun v _ => correctedVolume_nonneg (packet D n v) _ _ (region D n C v))
  intro v _
  exact correctedVolume_le_one (packet D n v) _ _ _
    ((packet D n v).normalizationHull_subset_normalization _ (Set.iUnion_subset (hunit v)))

include hw hunit in
theorem selectedPaperRootProduct_pow_le_volume :
    actualSelectedPaperRootNormProduct D ^ n ≤ volume D n C :=
  (FullSupportPaperWeightedHull.selectedPaperRootProduct_pow_le_volume D n).trans
    (base_volume_le D n C hw hunit)

include hw hunit in
theorem absLog_volume_le_mul_weightedPaperSum :
    |Real.log (volume D n C)| ≤ (n : ℝ) * FullSupportPaperWeightedHull.weightedPaperSum D := by
  have h := Real.log_le_log (FullSupportPaperWeightedHull.volume_pos D n)
    (base_volume_le D n C hw hunit)
  rw [abs_of_nonpos (Real.log_nonpos (volume_pos D n C hw hunit).le
    (volume_le_one D n C hunit)),
    ← FullSupportPaperWeightedHull.negLog_volume_eq_mul_weightedPaperSum D n]
  exact neg_le_neg h

include hw hunit in
theorem negAverageAbsLog_ge_neg_selectedPaperSum (hn : 0 < n) :
    -iutInitialThetaSelectedQRootPaperSum D ≤
      -(1 / (n : ℝ)) * |Real.log (volume D n C)| := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := mul_le_mul_of_nonneg_left (absLog_volume_le_mul_weightedPaperSum D n C hw hunit)
    (show 0 ≤ 1 / (n : ℝ) by positivity)
  rw [← mul_assoc, one_div_mul_cancel hn'.ne', one_mul] at h
  exact (neg_le_neg (FullSupportPaperWeightedHull.weightedPaperSum_le_selectedPaperSum D)).trans
    (by simpa only [neg_mul] using neg_le_neg h)

end
end JoshiTeich.Act1Scene1.FullSupportWitnessHull
