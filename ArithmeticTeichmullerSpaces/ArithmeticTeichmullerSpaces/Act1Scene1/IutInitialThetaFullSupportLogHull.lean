import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorLogGenerators
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFixedModuliNormalizationVolume
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRelativeQRootProduct
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadRootProductContracting

/-!
source-id: JT-SCENE1-INITIAL-THETA-FULL-SUPPORT-LOG-HULL
source: Joshi III complete section odd semistable locus (1028--1055),
multiplicative log-shell picture and normalized hull volume (3474--3631).
fidelity: constructs ordinary-log generators and actual normalization hulls
at every odd multiplicative moduli place using the canonical section. The
global Haar volume has exactly the full-support root accounting, without
VBad coverage or supplied place/tuple/measure certificates. Different untilts,
Bloch-Kato/theta loci and paper weighted-volume identities remain separate.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.FullSupportThetaLogHull
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (n : ℕ)

def sourceAt (v : iutInitialThetaOddModSupportFinset D) (_ : Fin n) :
    (iutInitialThetaOddSupportTorsionQRootSource D).badFinset :=
  (iutInitialThetaModuliSelectedSourceEquiv D v).1

theorem sourceAt_liesOver (v : iutInitialThetaOddModSupportFinset D) (i : Fin n) :
    Ideal.LiesOver (sourceAt D n v i).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal :=
  iutInitialThetaModuliSelectedSource_liesOver D v

local instance fullLogHullPrime (v : iutInitialThetaOddModSupportFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩

abbrev packet (v : iutInitialThetaOddModSupportFinset D) :=
  FixedModuliThetaTensor.packet D v (sourceAt D n v) (sourceAt_liesOver D n v)

local instance fullLogHullIntegralModule (v : iutInitialThetaOddModSupportFinset D) :
    Module ℤ_[Arithmetic.residueChar v.1] (packet D n v).Tensor :=
  Module.compHom (packet D n v).Tensor
    (algebraMap ℤ_[Arithmetic.residueChar v.1] ℚ_[Arithmetic.residueChar v.1])

def generators (v : iutInitialThetaOddModSupportFinset D) : Set (packet D n v).Tensor :=
  (packet D n v).logScalarGenerators
    (fun i => iutInitialThetaFullQRootLogValue D (sourceAt D n v i))

def region (v : iutInitialThetaOddModSupportFinset D) :
    Submodule (packet D n v).normalization (packet D n v).Tensor :=
  (packet D n v).normalizationHull (generators D n v)

def volume : ℝ :=
  (∏ v : iutInitialThetaOddModSupportFinset D,
    (packet D n v).normalizationDegreeVolume (region D n v) ^ Arithmetic.localDeg v.1) ^
    (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ))

theorem generators_eq_scalarGenerators (v : iutInitialThetaOddModSupportFinset D) :
    generators D n v = (packet D n v).scalarGenerators
      (fun i => iutInitialThetaFullQRootLogValue D (sourceAt D n v i)) :=
  (packet D n v).logScalarGenerators_eq_scalarGenerators _

theorem generators_subset_normalization (v : iutInitialThetaOddModSupportFinset D) :
    generators D n v ⊆ (packet D n v).normalization := by
  apply Set.Subset.trans _ (packet D n v).unitLattice_le_normalization
  apply (packet D n v).logScalarGenerators_subset_unitLattice
  intro i
  rw [iutInitialThetaFullQRootLogValue_norm_eq]
  exact (iutInitialThetaFullQRoot_norm_lt_one D _).le

theorem region_eq_scalarNormalization (v : iutInitialThetaOddModSupportFinset D) :
    (region D n v : Set (packet D n v).Tensor) =
      (FixedModuliThetaNormalization.region D v (sourceAt D n v) (sourceAt_liesOver D n v) :
        Set (packet D n v).Tensor) := by
  unfold region generators FixedModuliThetaNormalization.region
  apply (packet D n v).normalizationHull_logScalarGenerators _
    (fun i => norm_ne_zero_iff.mp (by
      rw [iutInitialThetaFullQRootLogValue_norm_eq]
      exact norm_ne_zero_iff.mpr
        ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero _)))

theorem region_isCompact (v : iutInitialThetaOddModSupportFinset D) :
    IsCompact (region D n v : Set (packet D n v).Tensor) := by
  rw [region_eq_scalarNormalization D n v]
  exact (packet D n v).scalarNormalization_isCompact _ _

theorem region_subset_normalization (v : iutInitialThetaOddModSupportFinset D) :
    (region D n v : Set (packet D n v).Tensor) ⊆ (packet D n v).normalization :=
  (packet D n v).normalizationHull_subset_normalization _ (generators_subset_normalization D n v)

theorem localVolume_eq_relativeFactor_pow (v : iutInitialThetaOddModSupportFinset D) :
    (packet D n v).normalizationDegreeVolume (region D n v) ^ Arithmetic.localDeg v.1 =
      iutInitialThetaRelativeQRootFactor D v ^ n := by
  rw [region_eq_scalarNormalization D n v]
  change FixedModuliThetaNormalization.volume D v (sourceAt D n v) (sourceAt_liesOver D n v) = _
  simpa only [Fintype.card_fin] using FixedModuliThetaNormalization.volume_eq_relativeFactor_pow
    D v (sourceAt D n v) (sourceAt_liesOver D n v)

theorem volume_eq_normalizedFullRootProduct_pow :
    volume D n = iutInitialThetaNormalizedRelativeQRootProduct D ^ n := by
  unfold volume
  simp only [localVolume_eq_relativeFactor_pow D n]
  rw [Finset.prod_pow, ← iutInitialThetaRelativeQRootProduct,
    ← Real.rpow_pow_comm (iutInitialThetaRelativeQRootProduct_pos D).le]
  rfl

theorem volume_pos : 0 < volume D n := by
  rw [volume_eq_normalizedFullRootProduct_pow]
  exact pow_pos (Real.rpow_pos_of_pos (iutInitialThetaRelativeQRootProduct_pos D) _) n

theorem negLog_volume_eq_mul_fullBaseSum :
    -Real.log (volume D n) = (n : ℝ) * iutInitialThetaFullBaseQPilotLogSum D := by
  rw [volume_eq_normalizedFullRootProduct_pow, Real.log_pow,
    ← iutInitialThetaNormalizedRelativeQRootProduct_negLog_eq_fullBaseSum D, mul_neg]

theorem volume_eq_exp_neg_fullBaseSum :
    volume D n = Real.exp (-((n : ℝ) * iutInitialThetaFullBaseQPilotLogSum D)) := by
  have hlog : Real.log (volume D n) = -((n : ℝ) * iutInitialThetaFullBaseQPilotLogSum D) :=
    calc
      _ = -(-Real.log (volume D n)) := (neg_neg _).symm
      _ = _ := congrArg Neg.neg (negLog_volume_eq_mul_fullBaseSum D n)
  rw [← hlog]
  exact (Real.exp_log (volume_pos D n)).symm

theorem volume_le_one : volume D n ≤ 1 := by
  have hfull : 0 ≤ iutInitialThetaFullBaseQPilotLogSum D :=
    (iutInitialThetaReferenceAbsLogQ_pos D).le.trans (iutInitialThetaReferenceAbsLogQ_le_fullBaseSum D)
  rw [volume_eq_exp_neg_fullBaseSum, Real.exp_le_one_iff]
  exact neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg n) hfull)

theorem absLog_volume_eq_mul_fullBaseSum :
    |Real.log (volume D n)| = (n : ℝ) * iutInitialThetaFullBaseQPilotLogSum D := by
  rw [abs_of_nonpos (Real.log_nonpos (volume_pos D n).le (volume_le_one D n))]
  exact negLog_volume_eq_mul_fullBaseSum D n

end
end JoshiTeich.Act1Scene1.FullSupportThetaLogHull
