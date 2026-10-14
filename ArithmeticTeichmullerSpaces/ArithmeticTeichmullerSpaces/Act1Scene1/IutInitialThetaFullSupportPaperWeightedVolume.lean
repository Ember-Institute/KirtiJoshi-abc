import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFullSupportLogHull
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedPaperRootNormProduct

/-!
source-id: JT-SCENE1-INITIAL-THETA-FULL-SUPPORT-PAPER-WEIGHTED-VOLUME
source: Joshi III ss:weighted-vol, le:volume-lemma2 and eq:weights
(3520--3557), and the complete section ordinary-log hull.
fidelity: constructs a numerical volume from actual normalization Haar on
each fixed-moduli block, with the selected residue-degree correction. It
proves the exact product of corrected root norms with inverse relative
completion-degree weights, over the complete support, without a global
degree root. This is a volume on this block presentation; mixed-moduli
tensor descent, different untilts, BK/theta loci and final source sign remain
separate obligations. No paper theta-volume identity is assumed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.FullSupportPaperWeightedHull
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (n : ℕ)

abbrev selected (v : iutInitialThetaOddModSupportFinset D) :=
  (iutInitialThetaModuliSelectedSourceEquiv D v).1

def weight (v : iutInitialThetaOddModSupportFinset D) : ℝ :=
  letI := LocalCompletion.relativeAlgebra (iutInitialThetaModuliSelectedSource_liesOver D v)
  1 / (Module.finrank
    (LocalCompletion.completionAt ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) v.1)
    (LocalCompletion.completionAt ↥D.prime.torsionField (selected D v).1) : ℝ)

theorem weight_eq_localDeg_ratio (v : iutInitialThetaOddModSupportFinset D) :
    weight D v = (Arithmetic.localDeg v.1 : ℝ) / Arithmetic.localDeg (selected D v).1 :=
  LocalCompletion.inverse_relativeFinrank_eq_localDeg_ratio
    (iutInitialThetaModuliSelectedSource_liesOver D v)

theorem weight_mem_Ioc (v : iutInitialThetaOddModSupportFinset D) :
    weight D v ∈ Set.Ioc (0 : ℝ) 1 :=
  LocalCompletion.inverse_relativeFinrank_mem_Ioc
    (iutInitialThetaModuliSelectedSource_liesOver D v)

def factor (v : iutInitialThetaOddModSupportFinset D) : ℝ :=
  actualPaperRootNorm D (selected D v) ^ weight D v

theorem factor_mem_Ioo (v : iutInitialThetaOddModSupportFinset D) :
    factor D v ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨Real.rpow_pos_of_pos (actualPaperRootNorm_mem_Ioo D _).1 _,
    Real.rpow_lt_one (actualPaperRootNorm_mem_Ioo D _).1.le
      (actualPaperRootNorm_mem_Ioo D _).2 (weight_mem_Ioc D v).1⟩

theorem paperRootNorm_le_factor (v : iutInitialThetaOddModSupportFinset D) :
    actualPaperRootNorm D (selected D v) ≤ factor D v :=
  Real.self_le_rpow_of_le_one (actualPaperRootNorm_mem_Ioo D _).1.le
    (actualPaperRootNorm_mem_Ioo D _).2.le (weight_mem_Ioc D v).2

theorem factor_eq_corrected_relativeFactor (v : iutInitialThetaOddModSupportFinset D) :
    factor D v = iutInitialThetaRelativeQRootFactor D v ^
      (1 / (Arithmetic.inertDeg (selected D v).1 : ℝ)) := by
  unfold factor actualPaperRootNorm
  rw [iutInitialThetaRelativeQRootFactor_eq_localDeg_ratio, weight_eq_localDeg_ratio,
    ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  ring

local instance weightedHullPrime (v : iutInitialThetaOddModSupportFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩

/-- A residue correction of the actual local Haar degree volume. -/
def localVolume (v : iutInitialThetaOddModSupportFinset D) : ℝ :=
  ((FullSupportThetaLogHull.packet D n v).normalizationDegreeVolume
    (FullSupportThetaLogHull.region D n v) ^ Arithmetic.localDeg v.1) ^
      (1 / (Arithmetic.inertDeg (selected D v).1 : ℝ))

theorem localVolume_eq_factor_pow (v : iutInitialThetaOddModSupportFinset D) :
    localVolume D n v = factor D v ^ n := by
  rw [localVolume, FullSupportThetaLogHull.localVolume_eq_relativeFactor_pow,
    factor_eq_corrected_relativeFactor,
    Real.rpow_pow_comm (iutInitialThetaRelativeQRootFactor_mem_Ioo D v).1.le]

/-- The complete block product, with no global degree normalization. -/
def volume : ℝ := ∏ v : iutInitialThetaOddModSupportFinset D, localVolume D n v

theorem volume_eq_factorProduct_pow :
    volume D n = (∏ v : iutInitialThetaOddModSupportFinset D, factor D v) ^ n := by
  simp only [volume, localVolume_eq_factor_pow, Finset.prod_pow]

theorem volume_pos : 0 < volume D n := by
  rw [volume_eq_factorProduct_pow]
  exact pow_pos (Finset.prod_pos fun v _ => (factor_mem_Ioo D v).1) n

theorem volume_le_one : volume D n ≤ 1 := by
  rw [volume_eq_factorProduct_pow]
  exact pow_le_one₀ (Finset.prod_nonneg fun v _ => (factor_mem_Ioo D v).1.le)
    (Finset.prod_le_one₀ (fun v _ => (factor_mem_Ioo D v).1.le)
      (fun v _ => (factor_mem_Ioo D v).2.le))

theorem selectedPaperRootProduct_eq_moduliProduct :
    actualSelectedPaperRootNormProduct D =
      ∏ v : iutInitialThetaOddModSupportFinset D, actualPaperRootNorm D (selected D v) := by
  letI : Fintype {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
      s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D} :=
    (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
  unfold actualSelectedPaperRootNormProduct
  exact ((iutInitialThetaModuliSelectedSourceEquiv D).prod_comp
    (fun s => actualPaperRootNorm D s.1)).symm

theorem selectedPaperRootProduct_pow_le_volume :
    actualSelectedPaperRootNormProduct D ^ n ≤ volume D n := by
  rw [volume_eq_factorProduct_pow, selectedPaperRootProduct_eq_moduliProduct]
  apply pow_le_pow_left₀ (Finset.prod_nonneg fun v _ =>
    (actualPaperRootNorm_mem_Ioo D (selected D v)).1.le)
  exact Finset.prod_le_prod₀ (fun v _ => (actualPaperRootNorm_mem_Ioo D _).1.le)
    (fun v _ => paperRootNorm_le_factor D v)

def weightedPaperSum : ℝ :=
  ∑ v : iutInitialThetaOddModSupportFinset D,
    weight D v * (-Real.log (actualPaperRootNorm D (selected D v)))

theorem negLog_volume_eq_mul_weightedPaperSum :
    -Real.log (volume D n) = (n : ℝ) * weightedPaperSum D := by
  rw [volume_eq_factorProduct_pow, Real.log_pow,
    Real.log_prod (fun v _ => (factor_mem_Ioo D v).1.ne'),
    ← mul_neg, ← Finset.sum_neg_distrib, weightedPaperSum]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  rw [factor, Real.log_rpow (actualPaperRootNorm_mem_Ioo D _).1, mul_neg]

theorem weightedPaperSum_le_selectedPaperSum :
    weightedPaperSum D ≤ iutInitialThetaSelectedQRootPaperSum D := by
  have hp : actualSelectedPaperRootNormProduct D ≤ volume D 1 := by
    simpa only [pow_one] using selectedPaperRootProduct_pow_le_volume D 1
  have h := Real.log_le_log (actualSelectedPaperRootNormProduct_mem_Ioo D).1
    hp
  have hc := negLog_volume_eq_mul_weightedPaperSum D 1
  simp only [Nat.cast_one, one_mul] at hc
  have hneg := neg_le_neg h
  rw [hc, actualSelectedPaperRootNormProduct_negLog_eq_paperSum D] at hneg
  exact hneg

theorem negAverageAbsLog_ge_neg_selectedPaperSum (hn : 0 < n) :
    -iutInitialThetaSelectedQRootPaperSum D ≤
      -(1 / (n : ℝ)) * |Real.log (volume D n)| := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [abs_of_nonpos (Real.log_nonpos (volume_pos D n).le (volume_le_one D n))]
  rw [show -Real.log (volume D n) = (n : ℝ) * weightedPaperSum D from
    negLog_volume_eq_mul_weightedPaperSum D n,
    neg_mul, ← mul_assoc, one_div_mul_cancel hn'.ne', one_mul]
  exact neg_le_neg (weightedPaperSum_le_selectedPaperSum D)

end
end JoshiTeich.Act1Scene1.FullSupportPaperWeightedHull
