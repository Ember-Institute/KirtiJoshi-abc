import ArithmeticTeichmullerSpaces.Act1Scene1.LocalPadicPaperLog
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorEqualNormHull
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFullSupportWitnessHull

/-!
source-id: JT-SCENE1-INITIAL-THETA-PSTAR-LOG-WITNESS-HULL
source: Joshi III eq:bloch-kato-log-class (3226) and the standard-point
witness used in form2 (3624--3631).
fidelity: constructs the actual principal unit 1+pStar*qroot and its ordinary
logarithm divided by p*, with the literal p* convention. Its singleton
normalization hull equals the previous 2p-log hull. Saturating a collation
therefore transfers the full corrected relative weighted volume bound
from a p*-log witness membership. BK cohomology, different untilts,
mixed-moduli descent and final thetaVolume/source sign remain open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.PaperLogWitnessHull
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (n : ℕ)

local instance paperLogCharZero (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (s.1.maximalIdeal.adicCompletion ↥D.prime.torsionField) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

def principalUnit (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :=
  LocalPadicLog.paperPrincipalUnit (Arithmetic.residueChar s.1)
    ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s)

def value (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :=
  LocalPadicLog.paperNormalizedLog (Arithmetic.residueChar s.1)
    ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s)

theorem principalUnit_norm_sub_one_lt_one
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ‖principalUnit D s - 1‖ < 1 :=
  LocalPadicLog.paperPrincipalUnit_norm_sub_one_lt_one (Arithmetic.residueChar_prime s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1) (iutInitialThetaFullQRoot_norm_lt_one D s).le

theorem value_eq_log_principalUnit
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    value D s = (LocalPadicLog.paperScale (Arithmetic.residueChar s.1) :
      s.1.maximalIdeal.adicCompletion ↥D.prime.torsionField)⁻¹ * LocalPadicLog.padicLog (principalUnit D s) := rfl

theorem norm_value_eq_qroot_norm
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ‖value D s‖ = ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot s‖ :=
  LocalPadicLog.norm_paperNormalizedLog (Arithmetic.residueChar_prime s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1) (iutInitialThetaFullQRoot_norm_lt_one D s).le

theorem value_ne_zero (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    value D s ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_value_eq_qroot_norm]
  exact norm_ne_zero_iff.mpr ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero s)

abbrev packet (v : iutInitialThetaOddModSupportFinset D) := FullSupportWitnessHull.packet D n v
local instance paperWitnessPrime (v : iutInitialThetaOddModSupportFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩

def witness (v : iutInitialThetaOddModSupportFinset D) : (packet D n v).Tensor :=
  (packet D n v).pure (fun i => value D (FullSupportThetaLogHull.sourceAt D n v i))

theorem witness_isUnit (v : iutInitialThetaOddModSupportFinset D) : IsUnit (witness D n v) :=
  (packet D n v).pure_isUnit _ (fun i => value_ne_zero D _)

theorem witness_hull_eq_base (v : iutInitialThetaOddModSupportFinset D) :
    ((packet D n v).normalizationHull {witness D n v} : Set (packet D n v).Tensor) =
      (FullSupportThetaLogHull.region D n v : Set (packet D n v).Tensor) := by
  rw [(packet D n v).normalizationHull_singleton_eq_principalRegion,
    FullSupportThetaLogHull.region_eq_scalarNormalization]
  change (packet D n v).principalRegion _ =
    ((packet D n v).scalarNormalization _ _ : Set (packet D n v).Tensor)
  unfold witness
  rw [← (packet D n v).scalarNormalization_eq_principalRegion
    (fun i => value D (FullSupportThetaLogHull.sourceAt D n v i)) (fun i => value_ne_zero D _)]
  apply (packet D n v).scalarNormalization_eq_of_norm_eq
  intro i
  rw [norm_value_eq_qroot_norm, iutInitialThetaFullQRootLogValue_norm_eq]

theorem witness_mem_base_region (v : iutInitialThetaOddModSupportFinset D) :
    witness D n v ∈ FullSupportThetaLogHull.region D n v := by
  change witness D n v ∈ (FullSupportThetaLogHull.region D n v : Set (packet D n v).Tensor)
  rw [← witness_hull_eq_base D n v]
  exact (packet D n v).subset_normalizationHull _ (Set.mem_singleton _)

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

def saturatedCollation (v : iutInitialThetaOddModSupportFinset D) (_ : Unit) :
    Set (packet D n v).Tensor := FullSupportWitnessHull.region D n C v

theorem saturated_region_eq (v : iutInitialThetaOddModSupportFinset D) :
    FullSupportWitnessHull.region D n (saturatedCollation D n C) v =
      FullSupportWitnessHull.region D n C v := by
  simp only [FullSupportWitnessHull.region, saturatedCollation, Set.iUnion_const,
    LocalCompletion.Packet.normalizationHull, Submodule.span_eq]

theorem saturated_volume_eq :
    FullSupportWitnessHull.volume D n (saturatedCollation D n C) = FullSupportWitnessHull.volume D n C := by
  unfold FullSupportWitnessHull.volume
  apply Finset.prod_congr rfl
  intro v _
  unfold FullSupportWitnessHull.localVolume
  rw [saturated_region_eq]

variable (hw : ∀ v, witness D n v ∈ ⋃ k, C v k)
variable (hunit : ∀ v k, C v k ⊆ (packet D n v).normalization)

include hw in
theorem base_region_subset_region (v : iutInitialThetaOddModSupportFinset D) :
    (FullSupportThetaLogHull.region D n v : Set (packet D n v).Tensor) ⊆
      FullSupportWitnessHull.region D n C v := by
  rw [← witness_hull_eq_base D n v]
  exact Submodule.span_mono (Set.singleton_subset_iff.mpr (hw v))

include hw hunit in
theorem saturatedCollation_laws :
    (∀ v, FullSupportWitnessHull.witness D n v ∈ ⋃ k, saturatedCollation D n C v k) ∧
      (∀ v k, saturatedCollation D n C v k ⊆ (packet D n v).normalization) := by
  constructor
  · intro v
    simp only [saturatedCollation, Set.iUnion_const]
    exact base_region_subset_region D n C hw v (FullSupportWitnessHull.witness_mem_base_region D n v)
  · intro v _
    exact (packet D n v).normalizationHull_subset_normalization _ (Set.iUnion_subset (hunit v))

include hw hunit in
theorem selectedPaperRootProduct_pow_le_volume :
    actualSelectedPaperRootNormProduct D ^ n ≤ FullSupportWitnessHull.volume D n C := by
  rw [← saturated_volume_eq D n C]
  exact FullSupportWitnessHull.selectedPaperRootProduct_pow_le_volume D n _
    (saturatedCollation_laws D n C hw hunit).1 (saturatedCollation_laws D n C hw hunit).2

include hw hunit in
theorem negAverageAbsLog_ge_neg_selectedPaperSum (hn : 0 < n) :
    -iutInitialThetaSelectedQRootPaperSum D ≤
      -(1 / (n : ℝ)) * |Real.log (FullSupportWitnessHull.volume D n C)| := by
  rw [← saturated_volume_eq D n C]
  exact FullSupportWitnessHull.negAverageAbsLog_ge_neg_selectedPaperSum D n _
    (saturatedCollation_laws D n C hw hunit).1 (saturatedCollation_laws D n C hw hunit).2 hn

end
end JoshiTeich.Act1Scene1.PaperLogWitnessHull
