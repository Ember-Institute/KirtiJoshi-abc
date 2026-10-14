import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadCollatedNormalizationVolume
import Mathlib.Tactic.Ring

/-!
source-id: JT-SCENE1-INITIAL-THETA-VBAD-HULL-LOG-MEASURE-TRANSFER
source: actual collated hull Haar product and Joshi III normalized Haar
log volumes/weighted products (3495--3557).
fidelity: computes actual global log volume as a sum of positive degree
weights times local log Haar measures. The measures are finite and positive;
normalization containment makes their log measures nonpositive. The explicit
local/global degree corrections are not a paper weighted-volume identity.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.VBadThetaHullLogTransfer
open JoshiTeich.Prologue MeasureTheory
open scoped BigOperators Classical
universe u
noncomputable section
private def normalizationLogMeasure
    {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {ι : Type} [Fintype ι] (P : LocalCompletion.Packet K p ι) (U : Set P.Tensor) : ℝ :=
  Real.log (P.normalizationHaar U).toReal

private theorem normalizationLogMeasure_nonpos
    {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {ι : Type} [Fintype ι] (P : LocalCompletion.Packet K p ι)
    (U : Set P.Tensor) (hU : U ⊆ P.normalization) : normalizationLogMeasure P U ≤ 0 := by
  unfold normalizationLogMeasure
  have hmu : P.normalizationHaar U ≤ 1 :=
    (measure_mono hU).trans_eq P.normalizationHaar_normalization
  exact Real.log_nonpos ENNReal.toReal_nonneg
    ((ENNReal.toReal_mono ENNReal.one_ne_top hmu).trans_eq ENNReal.toReal_one)

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (n : ℕ)
variable (σ : iutInitialThetaVBadModuliFinset D → Fin n →
  (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
variable (hσ : ∀ v i, Ideal.LiesOver (σ v i).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal)
local instance logTransferPrime (v : iutInitialThetaVBadModuliFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩
def packetLogWeight (v : iutInitialThetaVBadModuliFinset D) : ℝ :=
  Arithmetic.placeWeight v.1 /
    (Module.finrank ℚ_[Arithmetic.residueChar v.1] (VBadThetaCollatedHull.packet D n σ hσ v).Tensor : ℝ)

theorem packetLogWeight_pos (v : iutInitialThetaVBadModuliFinset D) :
    0 < packetLogWeight D n σ hσ v :=
  div_pos (Arithmetic.placeWeight_pos v.1)
    (by exact_mod_cast (VBadThetaCollatedHull.packet D n σ hσ v).tensor_finrank_pos)

variable {κ : Type*}
variable (C : ∀ v : iutInitialThetaVBadModuliFinset D,
  κ → Set (VBadThetaCollatedHull.packet D n σ hσ v).Tensor)

def packetLogVolume (v : iutInitialThetaVBadModuliFinset D) : ℝ :=
  normalizationLogMeasure (VBadThetaCollatedHull.packet D n σ hσ v)
    (VBadThetaCollatedHull.region D n σ hσ C v)

variable (hgen : ∀ v, (VBadThetaCollatedHull.packet D n σ hσ v).scalarGenerators
  (fun i => iutInitialThetaFullQRootLogValue D (σ v i)) ⊆ ⋃ k, C v k)
variable (hunit : ∀ v k, C v k ⊆ (VBadThetaCollatedHull.packet D n σ hσ v).normalization)

include hunit in
theorem packetLogVolume_nonpos (v : iutInitialThetaVBadModuliFinset D) :
    packetLogVolume D n σ hσ C v ≤ 0 := by
  unfold packetLogVolume
  apply normalizationLogMeasure_nonpos
  exact (VBadThetaCollatedHull.packet D n σ hσ v).normalizationHull_subset_normalization
    (⋃ k, C v k) (Set.iUnion_subset (hunit v))

include hgen hunit in
theorem log_volume_eq_weightedPacketLogs :
    Real.log (VBadThetaCollatedHull.volume D n σ hσ C) =
      ∑ v : iutInitialThetaVBadModuliFinset D,
        packetLogWeight D n σ hσ v * packetLogVolume D n σ hσ C v := by
  have hlocal (v : iutInitialThetaVBadModuliFinset D) :
      0 < (VBadThetaCollatedHull.packet D n σ hσ v).normalizationDegreeVolume
        (VBadThetaCollatedHull.region D n σ hσ C v) ^ Arithmetic.localDeg v.1 := by
    have h := FixedModuliThetaCollatedHull.relativeFactor_pow_le_volume
      D (iutInitialThetaVBadModuliAt D v) (σ v) (hσ v) (C v) (hgen v) (hunit v)
    simp only [Fintype.card_fin] at h
    exact (pow_pos (iutInitialThetaRelativeQRootFactor_mem_Ioo D (iutInitialThetaVBadModuliAt D v)).1 n).trans_le h
  have hreal (v : iutInitialThetaVBadModuliFinset D) :
      0 < ((VBadThetaCollatedHull.packet D n σ hσ v).normalizationHaar
        (VBadThetaCollatedHull.region D n σ hσ C v)).toReal :=
    ENNReal.toReal_pos (VBadThetaCollatedHull.region_haar_pos_lt_top D n σ hσ C hgen hunit v).1.ne'
      (VBadThetaCollatedHull.region_haar_pos_lt_top D n σ hσ C hgen hunit v).2.ne
  unfold VBadThetaCollatedHull.volume
  rw [Real.log_rpow (Finset.prod_pos fun v _ => hlocal v),
    Real.log_prod (fun v _ => (hlocal v).ne'), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [Real.log_pow, LocalCompletion.Packet.normalizationDegreeVolume, Real.log_rpow (hreal v)]
  unfold packetLogWeight packetLogVolume normalizationLogMeasure Arithmetic.placeWeight
  ring

include hunit in
theorem weightedPacketLogs_nonpos :
    (∑ v : iutInitialThetaVBadModuliFinset D,
      packetLogWeight D n σ hσ v * packetLogVolume D n σ hσ C v) ≤ 0 :=
  Finset.sum_nonpos fun v _ => mul_nonpos_of_nonneg_of_nonpos
    (packetLogWeight_pos D n σ hσ v).le (packetLogVolume_nonpos D n σ hσ C hunit v)

include hgen hunit in
theorem log_volume_nonpos : Real.log (VBadThetaCollatedHull.volume D n σ hσ C) ≤ 0 := by
  rw [log_volume_eq_weightedPacketLogs D n σ hσ C hgen hunit]
  exact weightedPacketLogs_nonpos D n σ hσ C hunit

end
end JoshiTeich.Act1Scene1.VBadThetaHullLogTransfer
