import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorWitnessScaleVolume
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaLogCalibration

/-!
source-id: JT-SCENE1-ACTUAL-ORDINARY-LOG-HULL-VOLUME
source: original actual Kummer logarithm, normalized paper witness and
normalization Haar with the existing relative/residue weights;
Joshi III 3226--3236, 3520--3574, 3624--3631.
fidelity: constructs the tensor witness of the ordinary logs of the original
actual integral classes. Its singleton hull volume is the old normalized
witness volume times an explicit pStar correction. The negative logarithm
acquires exactly the correction cost. No BK/theta identity is asserted.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (n : ℕ)
abbrev packet (v : iutInitialThetaOddModSupportFinset D) := PaperLogWitnessHull.packet D n v
local instance ordinaryHullPrime (v : iutInitialThetaOddModSupportFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩
local instance ordinaryHullCharZero (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (PrincipalUnitKummer.localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

def scalar (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    PrincipalUnitKummer.localField D s :=
  LocalPadicLog.padicLog (PaperLogWitnessHull.principalUnit D s)

theorem scalar_eq_scale_value (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    scalar D s = (LocalPadicLog.paperScale (Arithmetic.residueChar s.1) : PrincipalUnitKummer.localField D s) *
      PaperLogWitnessHull.value D s :=
  PrincipalUnitKummer.log_principalUnit_eq_scale_value D s

theorem scalar_ne_zero (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    scalar D s ≠ 0 := by
  rw [scalar_eq_scale_value]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (LocalPadicLog.paperScale_ne_zero (Arithmetic.residueChar_prime s.1)))
    (PaperLogWitnessHull.value_ne_zero D s)

theorem norm_scale_lt_one (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ‖(LocalPadicLog.paperScale (Arithmetic.residueChar s.1) : PrincipalUnitKummer.localField D s)‖ < 1 :=
  (LocalPadicLog.norm_paperScale_eq_norm_two_mul (Arithmetic.residueChar_prime s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1)).trans_lt
      (LocalPadicLog.norm_two_mul_lt_one (InitialThetaLogWitness.norm_residueChar_lt_one s.1))

theorem norm_scalar_lt_one (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ‖scalar D s‖ < 1 := by
  rw [scalar_eq_scale_value, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (norm_scale_lt_one D s).le).trans_lt
    (by rw [PaperLogWitnessHull.norm_value_eq_qroot_norm]; exact iutInitialThetaFullQRoot_norm_lt_one D s)

def witness (v : iutInitialThetaOddModSupportFinset D) : (packet D n v).Tensor :=
  (packet D n v).pure (fun i => scalar D (FullSupportThetaLogHull.sourceAt D n v i))

def region (v : iutInitialThetaOddModSupportFinset D) :=
  (packet D n v).normalizationHull {witness D n v}

theorem region_isCompact (v : iutInitialThetaOddModSupportFinset D) :
    IsCompact (region D n v : Set (packet D n v).Tensor) := by
  rw [region, witness, (packet D n v).normalizationHull_singleton_eq_principalRegion,
    ← (packet D n v).scalarNormalization_eq_principalRegion _ (fun i => scalar_ne_zero D _)]
  exact (packet D n v).scalarNormalization_isCompact _ _

def degreeCorrection (v : iutInitialThetaOddModSupportFinset D) : ℝ :=
  ∏ i : Fin n,
    ‖(LocalPadicLog.paperScale (Arithmetic.residueChar (FullSupportThetaLogHull.sourceAt D n v i).1) :
      (packet D n v).Factor i)‖ ^
        (1 / (Arithmetic.localDeg (FullSupportThetaLogHull.sourceAt D n v i).1 : ℝ))

theorem degreeCorrection_pos (v : iutInitialThetaOddModSupportFinset D) :
    0 < degreeCorrection D n v := by
  apply Finset.prod_pos
  intro i _
  exact Real.rpow_pos_of_pos (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr
    (LocalPadicLog.paperScale_ne_zero (Arithmetic.residueChar_prime _)))) _

theorem degreeCorrection_le_one (v : iutInitialThetaOddModSupportFinset D) :
    degreeCorrection D n v ≤ 1 := by
  apply Finset.prod_le_one₀ (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
  intro i _
  exact Real.rpow_le_one (norm_nonneg _) (norm_scale_lt_one D _).le (by positivity)

theorem region_degreeVolume_eq_corrected (v : iutInitialThetaOddModSupportFinset D) :
    (packet D n v).normalizationDegreeVolume (region D n v) =
      degreeCorrection D n v * (packet D n v).normalizationDegreeVolume
        (FullSupportThetaLogHull.region D n v) := by
  have he : witness D n v = (packet D n v).pure
      (fun i => (LocalPadicLog.paperScale (Arithmetic.residueChar (FullSupportThetaLogHull.sourceAt D n v i).1) :
        (packet D n v).Factor i) * PaperLogWitnessHull.value D (FullSupportThetaLogHull.sourceAt D n v i)) := by
    unfold witness
    congr 1
    funext i
    exact scalar_eq_scale_value D _
  rw [region, he, (packet D n v).normalizationDegreeVolume_singleton_scaled _ _
    (fun i => Nat.cast_ne_zero.mpr (LocalPadicLog.paperScale_ne_zero (Arithmetic.residueChar_prime _)))
    (fun i => (norm_scale_lt_one D _).le) (fun i => PaperLogWitnessHull.value_ne_zero D _)
    (fun i => by rw [PaperLogWitnessHull.norm_value_eq_qroot_norm]; exact iutInitialThetaFullQRoot_norm_lt_one D _)]
  change degreeCorrection D n v * (packet D n v).normalizationDegreeVolume
    ((packet D n v).normalizationHull {PaperLogWitnessHull.witness D n v}) = _
  rw [PaperLogWitnessHull.witness_hull_eq_base D n v]

def localCorrection (v : iutInitialThetaOddModSupportFinset D) : ℝ :=
  (degreeCorrection D n v ^ Arithmetic.localDeg v.1) ^
    (1 / (Arithmetic.inertDeg (FullSupportPaperWeightedHull.selected D v).1 : ℝ))

def localVolume (v : iutInitialThetaOddModSupportFinset D) : ℝ :=
  ((packet D n v).normalizationDegreeVolume (region D n v) ^ Arithmetic.localDeg v.1) ^
    (1 / (Arithmetic.inertDeg (FullSupportPaperWeightedHull.selected D v).1 : ℝ))

theorem localVolume_eq_corrected (v : iutInitialThetaOddModSupportFinset D) :
    localVolume D n v = localCorrection D n v * FullSupportPaperWeightedHull.localVolume D n v := by
  have hv : 0 ≤ (packet D n v).normalizationDegreeVolume (FullSupportThetaLogHull.region D n v) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  rw [localVolume, region_degreeVolume_eq_corrected, mul_pow,
    Real.mul_rpow (pow_nonneg (degreeCorrection_pos D n v).le _) (pow_nonneg hv _)]
  rfl

def correction : ℝ := ∏ v : iutInitialThetaOddModSupportFinset D, localCorrection D n v
def volume : ℝ := ∏ v : iutInitialThetaOddModSupportFinset D, localVolume D n v

theorem correction_pos : 0 < correction D n :=
  Finset.prod_pos fun v _ => Real.rpow_pos_of_pos (pow_pos (degreeCorrection_pos D n v) _) _

theorem correction_le_one : correction D n ≤ 1 := by
  apply Finset.prod_le_one₀ (fun v _ => Real.rpow_nonneg (pow_nonneg (degreeCorrection_pos D n v).le _) _)
  intro v _
  exact Real.rpow_le_one (pow_nonneg (degreeCorrection_pos D n v).le _)
    (pow_le_one₀ (degreeCorrection_pos D n v).le (degreeCorrection_le_one D n v)) (by positivity)

theorem volume_eq_corrected :
    volume D n = correction D n * FullSupportPaperWeightedHull.volume D n := by
  simp only [volume, correction, FullSupportPaperWeightedHull.volume, localVolume_eq_corrected, Finset.prod_mul_distrib]

theorem volume_pos : 0 < volume D n := by
  rw [volume_eq_corrected]
  exact mul_pos (correction_pos D n) (FullSupportPaperWeightedHull.volume_pos D n)

theorem volume_le_normalized : volume D n ≤ FullSupportPaperWeightedHull.volume D n := by
  rw [volume_eq_corrected]
  exact mul_le_of_le_one_left (FullSupportPaperWeightedHull.volume_pos D n).le (correction_le_one D n)

theorem negLog_volume_eq_normalized_add_correction :
    -Real.log (volume D n) = -Real.log (FullSupportPaperWeightedHull.volume D n) - Real.log (correction D n) := by
  rw [volume_eq_corrected, Real.log_mul (correction_pos D n).ne'
    (FullSupportPaperWeightedHull.volume_pos D n).ne']
  ring

theorem negLog_volume_eq_weightedSum_add_correction :
    -Real.log (volume D n) = (n : ℝ) * FullSupportPaperWeightedHull.weightedPaperSum D - Real.log (correction D n) := by
  rw [negLog_volume_eq_normalized_add_correction, FullSupportPaperWeightedHull.negLog_volume_eq_mul_weightedPaperSum]

end
end JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
