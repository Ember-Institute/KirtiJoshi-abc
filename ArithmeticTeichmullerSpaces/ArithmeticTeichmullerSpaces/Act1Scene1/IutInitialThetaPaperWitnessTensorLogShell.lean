import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPaperLogShellBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensor
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorLogShellHull
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorTopology
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorOrder
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorNormalizationHull
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorWitnessHull
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorHullNormalizationBounds
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadRepresentativeBound
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRepresentativeRamificationGap
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFullSupportHullPaperBound

/-!
source-id: JT-SCENE1-PAPER-WITNESS-TENSOR-LOG-SHELL
source: actual full-support paper-normalized witnesses and the tensor
log-shell carrier used by the ordinary hull construction.
fidelity: lifts the factorwise paper-normalized log-shell membership to the
actual pure tensor witness. This is a tensor carrier statement only; it does
not identify the tensor log-shell with H^1_e/BK or with a paper theta locus.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.PaperLogWitnessHull
open JoshiTeich.Prologue
open scoped Valued
universe u
noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (n : ℕ)

local instance paperTensorPrime (v : iutInitialThetaOddModSupportFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩

theorem witness_integralHull_normalizationHull_eq_base
    (v : iutInitialThetaOddModSupportFinset D) :
    ((packet D n v).normalizationHull
      ((packet D n v).integralHull {witness D n v}) : Set (packet D n v).Tensor) =
      (FullSupportThetaLogHull.region D n v : Set (packet D n v).Tensor) := by
  rw [(packet D n v).normalizationHull_integralHull, witness_hull_eq_base D n v]

theorem witness_integralHull_normalizationDegreeVolume_eq_base
    (v : iutInitialThetaOddModSupportFinset D) :
    (packet D n v).normalizationDegreeVolume
        ((packet D n v).normalizationHull
          ((packet D n v).integralHull {witness D n v})) =
      (packet D n v).normalizationDegreeVolume
        (FullSupportThetaLogHull.region D n v) := by
  rw [witness_integralHull_normalizationHull_eq_base D n v]

theorem witness_integralHull_localVolume_eq_relativeFactor_pow
    (v : iutInitialThetaOddModSupportFinset D) :
    ((packet D n v).normalizationDegreeVolume
        ((packet D n v).normalizationHull
          ((packet D n v).integralHull {witness D n v})) ^ Arithmetic.localDeg v.1) =
      iutInitialThetaRelativeQRootFactor D v ^ n := by
  rw [witness_integralHull_normalizationDegreeVolume_eq_base D n v]
  exact FullSupportThetaLogHull.localVolume_eq_relativeFactor_pow D n v

theorem witness_integralHull_localVolume_product_eq_relativeQRootProduct_pow :
    (∏ v : iutInitialThetaOddModSupportFinset D,
      (packet D n v).normalizationDegreeVolume
        ((packet D n v).normalizationHull
          ((packet D n v).integralHull {witness D n v})) ^ Arithmetic.localDeg v.1) =
      iutInitialThetaRelativeQRootProduct D ^ n := by
  calc
    (∏ v : iutInitialThetaOddModSupportFinset D,
        (packet D n v).normalizationDegreeVolume
          ((packet D n v).normalizationHull
            ((packet D n v).integralHull {witness D n v})) ^ Arithmetic.localDeg v.1) =
        ∏ v : iutInitialThetaOddModSupportFinset D,
          iutInitialThetaRelativeQRootFactor D v ^ n := by
      apply Finset.prod_congr rfl
      intro v hv
      exact witness_integralHull_localVolume_eq_relativeFactor_pow D n v
    _ = (∏ v : iutInitialThetaOddModSupportFinset D,
        iutInitialThetaRelativeQRootFactor D v) ^ n := by
      rw [Finset.prod_pow]
    _ = iutInitialThetaRelativeQRootProduct D ^ n := by
      rfl

theorem witness_integralHull_globalVolume_eq_normalizedRelativeQRootProduct_pow :
    (∏ v : iutInitialThetaOddModSupportFinset D,
      (packet D n v).normalizationDegreeVolume
        ((packet D n v).normalizationHull
          ((packet D n v).integralHull {witness D n v})) ^ Arithmetic.localDeg v.1) ^
        (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ)) =
      iutInitialThetaNormalizedRelativeQRootProduct D ^ n := by
  rw [witness_integralHull_localVolume_product_eq_relativeQRootProduct_pow D n,
    iutInitialThetaNormalizedRelativeQRootProduct,
    ← Real.rpow_pow_comm (iutInitialThetaRelativeQRootProduct_pos D).le]

theorem witness_integralHull_globalVolume_eq_fullSupport_volume :
    (∏ v : iutInitialThetaOddModSupportFinset D,
      (packet D n v).normalizationDegreeVolume
        ((packet D n v).normalizationHull
          ((packet D n v).integralHull {witness D n v})) ^ Arithmetic.localDeg v.1) ^
        (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ)) =
      FullSupportThetaLogHull.volume D n := by
  rw [witness_integralHull_globalVolume_eq_normalizedRelativeQRootProduct_pow D n,
    FullSupportThetaLogHull.volume_eq_normalizedFullRootProduct_pow D n]

theorem witness_integralHull_globalVolume_negLog_eq_mul_fullBaseSum :
    -Real.log
        ((∏ v : iutInitialThetaOddModSupportFinset D,
          (packet D n v).normalizationDegreeVolume
            ((packet D n v).normalizationHull
              ((packet D n v).integralHull {witness D n v})) ^ Arithmetic.localDeg v.1) ^
          (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ))) =
      (n : ℝ) * iutInitialThetaFullBaseQPilotLogSum D := by
  rw [witness_integralHull_globalVolume_eq_fullSupport_volume D n,
    FullSupportThetaLogHull.negLog_volume_eq_mul_fullBaseSum D n]

theorem witness_integralHull_globalVolume_absLog_eq_mul_fullBaseSum :
    |Real.log
        ((∏ v : iutInitialThetaOddModSupportFinset D,
          (packet D n v).normalizationDegreeVolume
            ((packet D n v).normalizationHull
              ((packet D n v).integralHull {witness D n v})) ^ Arithmetic.localDeg v.1) ^
          (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ)))| =
      (n : ℝ) * iutInitialThetaFullBaseQPilotLogSum D := by
  rw [witness_integralHull_globalVolume_eq_fullSupport_volume D n,
    FullSupportThetaLogHull.absLog_volume_eq_mul_fullBaseSum D n]

theorem witness_integralHull_globalVolume_negLog_ge_mul_referenceAbsLogQ :
    -Real.log
        ((∏ v : iutInitialThetaOddModSupportFinset D,
          (packet D n v).normalizationDegreeVolume
            ((packet D n v).normalizationHull
              ((packet D n v).integralHull {witness D n v})) ^ Arithmetic.localDeg v.1) ^
          (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ))) ≥
      (n : ℝ) * JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  rw [witness_integralHull_globalVolume_negLog_eq_mul_fullBaseSum D n]
  exact mul_le_mul_of_nonneg_left
    (iutInitialThetaReferenceAbsLogQ_le_fullBaseSum D)
    (Nat.cast_nonneg n)

theorem witness_integralHull_globalVolume_negLog_lt_mul_selectedPaperSum
    (hn : 0 < n) :
    -Real.log
        ((∏ v : iutInitialThetaOddModSupportFinset D,
          (packet D n v).normalizationDegreeVolume
            ((packet D n v).normalizationHull
              ((packet D n v).integralHull {witness D n v})) ^ Arithmetic.localDeg v.1) ^
          (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ))) <
      (n : ℝ) * iutInitialThetaSelectedQRootPaperSum D := by
  rw [witness_integralHull_globalVolume_negLog_eq_mul_fullBaseSum D n]
  exact mul_lt_mul_of_pos_left
    (iutInitialThetaFullBaseQPilotLogSum_lt_selectedPaperSum D)
    (by exact_mod_cast hn)

theorem witness_integralHull_globalVolume_selectedPaperRootProduct_pow_lt
    (hn : 0 < n) :
    actualSelectedPaperRootNormProduct D ^ n <
      (∏ v : iutInitialThetaOddModSupportFinset D,
        (packet D n v).normalizationDegreeVolume
          ((packet D n v).normalizationHull
            ((packet D n v).integralHull {witness D n v})) ^ Arithmetic.localDeg v.1) ^
        (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ)) := by
  rw [witness_integralHull_globalVolume_eq_fullSupport_volume D n]
  exact FullSupportThetaLogHull.selectedPaperRootProduct_pow_lt_volume D n hn

theorem witness_integralHull_globalVolume_pos :
    0 <
      (∏ v : iutInitialThetaOddModSupportFinset D,
        (packet D n v).normalizationDegreeVolume
          ((packet D n v).normalizationHull
            ((packet D n v).integralHull {witness D n v})) ^ Arithmetic.localDeg v.1) ^
        (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ)) := by
  rw [witness_integralHull_globalVolume_eq_fullSupport_volume D n]
  exact FullSupportThetaLogHull.volume_pos D n

theorem witness_integralHull_globalVolume_le_one :
    (∏ v : iutInitialThetaOddModSupportFinset D,
      (packet D n v).normalizationDegreeVolume
        ((packet D n v).normalizationHull
          ((packet D n v).integralHull {witness D n v})) ^ Arithmetic.localDeg v.1) ^
        (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ)) ≤ 1 := by
  rw [witness_integralHull_globalVolume_eq_fullSupport_volume D n]
  exact FullSupportThetaLogHull.volume_le_one D n

theorem witness_integralHull_globalVolume_log_nonpos :
    Real.log
        ((∏ v : iutInitialThetaOddModSupportFinset D,
          (packet D n v).normalizationDegreeVolume
            ((packet D n v).normalizationHull
              ((packet D n v).integralHull {witness D n v})) ^ Arithmetic.localDeg v.1) ^
          (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ))) ≤ 0 :=
  Real.log_nonpos
    (witness_integralHull_globalVolume_pos D n).le
    (witness_integralHull_globalVolume_le_one D n)

theorem witness_integralHull_globalVolume_negLog_nonneg :
    0 ≤ -Real.log
        ((∏ v : iutInitialThetaOddModSupportFinset D,
          (packet D n v).normalizationDegreeVolume
            ((packet D n v).normalizationHull
              ((packet D n v).integralHull {witness D n v})) ^ Arithmetic.localDeg v.1) ^
          (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ))) :=
  neg_nonneg.mpr (witness_integralHull_globalVolume_log_nonpos D n)

theorem witness_integralHull_globalVolume_absLog_eq_negLog :
    |Real.log
        ((∏ v : iutInitialThetaOddModSupportFinset D,
          (packet D n v).normalizationDegreeVolume
            ((packet D n v).normalizationHull
              ((packet D n v).integralHull {witness D n v})) ^ Arithmetic.localDeg v.1) ^
          (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ)))| =
      -Real.log
        ((∏ v : iutInitialThetaOddModSupportFinset D,
          (packet D n v).normalizationDegreeVolume
            ((packet D n v).normalizationHull
              ((packet D n v).integralHull {witness D n v})) ^ Arithmetic.localDeg v.1) ^
          (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ))) := by
  rw [abs_of_nonpos (witness_integralHull_globalVolume_log_nonpos D n)]

theorem witness_integralHull_globalVolume_negLog_eq_absLog :
    -Real.log
        ((∏ v : iutInitialThetaOddModSupportFinset D,
          (packet D n v).normalizationDegreeVolume
            ((packet D n v).normalizationHull
              ((packet D n v).integralHull {witness D n v})) ^ Arithmetic.localDeg v.1) ^
          (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ))) =
      |Real.log
        ((∏ v : iutInitialThetaOddModSupportFinset D,
          (packet D n v).normalizationDegreeVolume
            ((packet D n v).normalizationHull
              ((packet D n v).integralHull {witness D n v})) ^ Arithmetic.localDeg v.1) ^
          (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ)))| :=
  (witness_integralHull_globalVolume_absLog_eq_negLog D n).symm

theorem witness_integralHull_globalVolume_absLog_ge_mul_referenceAbsLogQ :
    |Real.log
        ((∏ v : iutInitialThetaOddModSupportFinset D,
          (packet D n v).normalizationDegreeVolume
            ((packet D n v).normalizationHull
              ((packet D n v).integralHull {witness D n v})) ^ Arithmetic.localDeg v.1) ^
          (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ)))| ≥
      (n : ℝ) * JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  rw [witness_integralHull_globalVolume_absLog_eq_negLog D n]
  exact witness_integralHull_globalVolume_negLog_ge_mul_referenceAbsLogQ D n

theorem witness_integralHull_globalVolume_absLog_lt_mul_selectedPaperSum
    (hn : 0 < n) :
    |Real.log
        ((∏ v : iutInitialThetaOddModSupportFinset D,
          (packet D n v).normalizationDegreeVolume
            ((packet D n v).normalizationHull
              ((packet D n v).integralHull {witness D n v})) ^ Arithmetic.localDeg v.1) ^
          (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ)))| <
      (n : ℝ) * iutInitialThetaSelectedQRootPaperSum D := by
  rw [witness_integralHull_globalVolume_absLog_eq_mul_fullBaseSum D n]
  exact mul_lt_mul_of_pos_left
    (iutInitialThetaFullBaseQPilotLogSum_lt_selectedPaperSum D)
    (by exact_mod_cast hn : (0 : ℝ) < n)

theorem witness_integralHull_globalVolume_negAverageAbsLog_le_neg_referenceAbsLogQ
    (hn : 0 < n) :
    -(1 / (n : ℝ)) *
        |Real.log
          ((∏ v : iutInitialThetaOddModSupportFinset D,
            (packet D n v).normalizationDegreeVolume
              ((packet D n v).normalizationHull
                ((packet D n v).integralHull {witness D n v})) ^ Arithmetic.localDeg v.1) ^
            (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ)))| ≤
      -JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := mul_le_mul_of_nonneg_left
    (witness_integralHull_globalVolume_negLog_ge_mul_referenceAbsLogQ D n)
    (show 0 ≤ 1 / (n : ℝ) by positivity)
  have hcancel :
      (1 / (n : ℝ)) * ((n : ℝ) *
        JoshiTeich.ReferenceIut.QPilotData.absLogQ
          (IutTorsionQRootSource.iutInitialThetaQPilotData D)) =
        JoshiTeich.ReferenceIut.QPilotData.absLogQ
          (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
    rw [← mul_assoc, one_div_mul_cancel hn'.ne', one_mul]
  rw [hcancel] at h
  rw [witness_integralHull_globalVolume_negLog_eq_absLog D n] at h
  simpa only [neg_mul] using neg_le_neg h

theorem witness_integralHull_globalVolume_negAverageAbsLog_gt_neg_selectedPaperSum
    (hn : 0 < n) :
    -iutInitialThetaSelectedQRootPaperSum D <
      -(1 / (n : ℝ)) *
        |Real.log
          ((∏ v : iutInitialThetaOddModSupportFinset D,
            (packet D n v).normalizationDegreeVolume
              ((packet D n v).normalizationHull
                ((packet D n v).integralHull {witness D n v})) ^ Arithmetic.localDeg v.1) ^
            (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ)))| := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := mul_lt_mul_of_pos_left
    (witness_integralHull_globalVolume_negLog_lt_mul_selectedPaperSum D n hn)
    (show 0 < 1 / (n : ℝ) by positivity)
  have hcancel :
      (1 / (n : ℝ)) * ((n : ℝ) * iutInitialThetaSelectedQRootPaperSum D) =
        iutInitialThetaSelectedQRootPaperSum D := by
    rw [← mul_assoc, one_div_mul_cancel hn'.ne', one_mul]
  rw [hcancel] at h
  rw [witness_integralHull_globalVolume_negLog_eq_absLog D n] at h
  simpa only [neg_mul] using neg_lt_neg h

theorem witness_mem_tensorLogShell
    (v : iutInitialThetaOddModSupportFinset D) :
    witness D n v ∈ (packet D n v).tensorLogShell := by
  apply (packet D n v).pure_mem_lattice
  intro i
  have h := value_mem_logShell D (FullSupportThetaLogHull.sourceAt D n v i)
  rw [Arithmetic.residueChar_eq_of_liesOver
    (FullSupportThetaLogHull.sourceAt_liesOver D n v i)] at h
  exact h

theorem witness_integralHull_le_unitLattice
    (v : iutInitialThetaOddModSupportFinset D) :
    (packet D n v).integralHull {witness D n v} ≤ (packet D n v).unitLattice := by
  apply (packet D n v).integralHull_le_unitLattice
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  apply (packet D n v).pure_mem_lattice
  intro i
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [norm_value_eq_qroot_norm]
  exact (iutInitialThetaFullQRoot_norm_lt_one D _).le

theorem witness_integralHull_le_tensorLogShell
    (v : iutInitialThetaOddModSupportFinset D) :
    (packet D n v).integralHull {witness D n v} ≤ (packet D n v).tensorLogShell := by
  apply (packet D n v).integralHull_le_tensorLogShell
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  change witness D n v ∈ (packet D n v).tensorLogShell
  exact witness_mem_tensorLogShell D n v

theorem witness_integralHull_le_unitLattice_inf_tensorLogShell
    (v : iutInitialThetaOddModSupportFinset D) :
    (packet D n v).integralHull {witness D n v} ≤
      (packet D n v).unitLattice ⊓ (packet D n v).tensorLogShell := by
  exact le_inf (witness_integralHull_le_unitLattice D n v)
    (witness_integralHull_le_tensorLogShell D n v)

theorem witness_integralHull_isBounded
    (v : iutInitialThetaOddModSupportFinset D) :
    Bornology.IsBounded ((packet D n v).integralHull {witness D n v} :
      Set (packet D n v).Tensor) := by
  exact (packet D n v).unitLattice_isBounded.subset
    (witness_integralHull_le_unitLattice D n v)

theorem witness_integralHull_le_normalization
    (v : iutInitialThetaOddModSupportFinset D) :
    (packet D n v).integralHull {witness D n v} ≤
      (packet D n v).normalization.toSubmodule :=
  (witness_integralHull_le_unitLattice D n v).trans
    (packet D n v).unitLattice_le_normalization

theorem witness_integralHull_normalizationHull_subset_normalization
    (v : iutInitialThetaOddModSupportFinset D) :
    ((packet D n v).normalizationHull
      ((packet D n v).integralHull {witness D n v}) : Set (packet D n v).Tensor) ⊆
      (packet D n v).normalization :=
  (packet D n v).normalizationHull_subset_normalization _
    (witness_integralHull_le_normalization D n v)

theorem witness_integralHull_normalizationHull_haar_pos_lt_top
    (v : iutInitialThetaOddModSupportFinset D) :
    0 < (packet D n v).normalizationHaar
        ((packet D n v).normalizationHull
          ((packet D n v).integralHull {witness D n v})) ∧
      (packet D n v).normalizationHaar
        ((packet D n v).normalizationHull
          ((packet D n v).integralHull {witness D n v})) < ⊤ := by
  apply (packet D n v).normalizationHull_haar_pos_lt_top_of_pure_mem
    ((packet D n v).integralHull {witness D n v})
    (fun i => value D (FullSupportThetaLogHull.sourceAt D n v i))
    (fun i => value_ne_zero D _)
  · change witness D n v ∈ (packet D n v).integralHull {witness D n v}
    exact Submodule.subset_span (Set.mem_singleton _)
  · exact witness_integralHull_le_normalization D n v

theorem witness_integralHull_normalizationDegreeVolume_pos
    (v : iutInitialThetaOddModSupportFinset D) :
    0 < (packet D n v).normalizationDegreeVolume
        ((packet D n v).normalizationHull
          ((packet D n v).integralHull {witness D n v})) := by
  rw [LocalCompletion.Packet.normalizationDegreeVolume]
  exact Real.rpow_pos_of_pos
    (ENNReal.toReal_pos
      (witness_integralHull_normalizationHull_haar_pos_lt_top D n v).1.ne'
      (witness_integralHull_normalizationHull_haar_pos_lt_top D n v).2.ne) _

theorem witness_integralHull_normalizationDegreeVolume_le_one
    (v : iutInitialThetaOddModSupportFinset D) :
    (packet D n v).normalizationDegreeVolume
        ((packet D n v).normalizationHull
          ((packet D n v).integralHull {witness D n v})) ≤ 1 :=
  (packet D n v).normalizationDegreeVolume_le_one _
    (witness_integralHull_normalizationHull_subset_normalization D n v)

theorem witness_integralHull_normalizationDegreeVolume_log_nonpos
    (v : iutInitialThetaOddModSupportFinset D) :
    Real.log
        ((packet D n v).normalizationDegreeVolume
          ((packet D n v).normalizationHull
            ((packet D n v).integralHull {witness D n v}))) ≤ 0 :=
  Real.log_nonpos
    (witness_integralHull_normalizationDegreeVolume_pos D n v).le
    (witness_integralHull_normalizationDegreeVolume_le_one D n v)

theorem witness_integralHull_normalizationDegreeVolume_negLog_nonneg
    (v : iutInitialThetaOddModSupportFinset D) :
    0 ≤ -Real.log
        ((packet D n v).normalizationDegreeVolume
          ((packet D n v).normalizationHull
            ((packet D n v).integralHull {witness D n v}))) :=
  neg_nonneg.mpr (witness_integralHull_normalizationDegreeVolume_log_nonpos D n v)

theorem witness_integralHull_degreeVolume_le_normalizationHull_degreeVolume
    (v : iutInitialThetaOddModSupportFinset D) :
    (packet D n v).degreeVolume
        ((packet D n v).scalarLattice
          (fun i => value D (FullSupportThetaLogHull.sourceAt D n v i))) ≤
      (packet D n v).normalizationDegreeVolume
        ((packet D n v).normalizationHull
          ((packet D n v).integralHull {witness D n v})) := by
  apply (packet D n v).degreeVolume_le_normalizationHull_of_pure_mem
    ((packet D n v).integralHull {witness D n v})
    (fun i => value D (FullSupportThetaLogHull.sourceAt D n v i))
    (fun i => value_ne_zero D _)
  · change witness D n v ∈ (packet D n v).integralHull {witness D n v}
    exact Submodule.subset_span (Set.mem_singleton _)
  · exact witness_integralHull_le_normalization D n v

theorem witness_integralHull_normalizationHull_negLog_le_scalarLattice_negLog
    (v : iutInitialThetaOddModSupportFinset D) :
    -Real.log
        ((packet D n v).normalizationDegreeVolume
          ((packet D n v).normalizationHull
            ((packet D n v).integralHull {witness D n v}))) ≤
      -Real.log
        ((packet D n v).degreeVolume
          ((packet D n v).scalarLattice
            (fun i => value D (FullSupportThetaLogHull.sourceAt D n v i)))) := by
  have hScalarPos :
      0 < (packet D n v).degreeVolume
        ((packet D n v).scalarLattice
          (fun i => value D (FullSupportThetaLogHull.sourceAt D n v i))) := by
    rw [(packet D n v).degreeVolume_scalarLattice_eq_norm_product
      (fun i => value D (FullSupportThetaLogHull.sourceAt D n v i))
      (fun i => value_ne_zero D _)
      (fun i => by
        rw [norm_value_eq_qroot_norm]
        exact iutInitialThetaFullQRoot_norm_lt_one D _)]
    exact Finset.prod_pos (fun i hi => Real.rpow_pos_of_pos
      (norm_pos_iff.mpr (value_ne_zero D _)) _)
  exact neg_le_neg (Real.log_le_log
    hScalarPos
    (witness_integralHull_degreeVolume_le_normalizationHull_degreeVolume D n v))

end
end JoshiTeich.Act1Scene1.PaperLogWitnessHull
