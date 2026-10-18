import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorSaturatedLogShell
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFinitePacketHull

/-!
source-id: JT-SCENE1-INITIAL-THETA-FINITE-PACKET-LOG-SHELL
source: reference LocalConstruct/LogShell, integral_subset_logShell and
isCompact_logShell; Concrete/Container, logShell, and ThetaRegion,
thetaComponent_subset_logShell. Joshi III tensor log-shells and weighted volume.
fidelity: for the same actual D and every prime/capsule tuple, uses the
constructed normalization-saturated ordinary log-shell. Proves product
compactness, positive finite Haar, source/hull containment and weighted
log-volume comparison with its actual product Haar. Finite support and
paper BK/theta/log-shell identity remain separate obligations.
Original consumer proofs; no reference source code copied.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.IutInitialThetaFinitePacketLogShell

open JoshiTeich.Prologue MeasureTheory IutInitialThetaFinitePacketRegion
open scoped BigOperators Classical

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.property⟩
local instance fiberFinite (p : Nat.Primes) : Finite (Fiber D p) := Arithmetic.fiber_finite (p : ℕ)
local instance fiberFintype (p : Nat.Primes) : Fintype (Fiber D p) := Fintype.ofFinite _

def componentShell (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    Set (packet D p j c).Tensor := (packet D p j c).saturatedLogShell

def region (p : Nat.Primes) (j : ℕ) : Set (Total D p j) :=
  Set.pi Set.univ (componentShell D p j)

theorem region_isCompact (p : Nat.Primes) (j : ℕ) : IsCompact (region D p j) :=
  isCompact_univ_pi fun c => (packet D p j c).saturatedLogShell_isCompact

theorem integralRegion_subset (p : Nat.Primes) (j : ℕ) :
    integralRegion D p j ⊆ region D p j :=
  Set.pi_mono fun c _ => (packet D p j c).normalization_subset_saturatedLogShell

theorem source_region_subset (p : Nat.Primes) (j : ℕ) :
    IutInitialThetaFinitePacketRegion.region D p j ⊆ region D p j :=
  (IutInitialThetaFinitePacketRegion.region_subset_integralRegion D p j).trans
    (integralRegion_subset D p j)

theorem hull_region_subset (p : Nat.Primes) (j : ℕ) :
    IutInitialThetaFinitePacketHull.region D p j ⊆ region D p j :=
  (IutInitialThetaFinitePacketHull.region_subset_integralRegion D p j).trans
    (integralRegion_subset D p j)

theorem productMeasure_region (p : Nat.Primes) (j : ℕ) :
    productMeasure D p j (region D p j) =
      ∏ c : Tuple D p j, (packet D p j c).normalizationHaar (componentShell D p j c) :=
  Measure.pi_pi _ _

theorem productMeasure_region_pos_lt_top (p : Nat.Primes) (j : ℕ) :
    0 < productMeasure D p j (region D p j) ∧ productMeasure D p j (region D p j) < ⊤ := by
  rw [productMeasure_region]
  exact ⟨bot_lt_iff_ne_bot.mpr (Finset.prod_ne_zero_iff.mpr
    fun c _ => (packet D p j c).saturatedLogShell_haar_pos_lt_top.1.ne'),
    ENNReal.prod_lt_top fun c _ => (packet D p j c).saturatedLogShell_haar_pos_lt_top.2⟩

theorem one_le_productMeasure_region (p : Nat.Primes) (j : ℕ) :
    1 ≤ productMeasure D p j (region D p j) := by
  rw [← productMeasure_integralRegion D p j]
  exact measure_mono (integralRegion_subset D p j)

def packetLogVolume (p : Nat.Primes) (j : ℕ) : ℝ := ∑ c : Tuple D p j,
  IutInitialThetaFinitePacketLogVolume.tupleWeight D p j c *
    IutInitialThetaFinitePacketLogVolume.componentLogVolume D p j c (componentShell D p j c)

theorem packetLogVolume_eq_productMeasure_log (p : Nat.Primes) (j : ℕ) :
    packetLogVolume D p j = Real.log (productMeasure D p j (region D p j)).toReal /
      (Module.finrank ℚ ↥D.prime.torsionField : ℝ) ^ (j + 1) := by
  calc
    _ = (∑ c : Tuple D p j, Real.log ((packet D p j c).normalizationHaar
        (componentShell D p j c)).toReal) /
          (Module.finrank ℚ ↥D.prime.torsionField : ℝ) ^ (j + 1) := by
      simp only [packetLogVolume, IutInitialThetaFinitePacketLogVolume.weighted_componentLogVolume,
        Finset.sum_div]
    _ = _ := by
      rw [productMeasure_region, ENNReal.toReal_prod, Real.log_prod]
      intro c _
      exact (ENNReal.toReal_pos (packet D p j c).saturatedLogShell_haar_pos_lt_top.1.ne'
        (packet D p j c).saturatedLogShell_haar_pos_lt_top.2.ne).ne'

theorem packetLogVolume_nonneg (p : Nat.Primes) (j : ℕ) : 0 ≤ packetLogVolume D p j := by
  apply Finset.sum_nonneg
  intro c _
  exact mul_nonneg (IutInitialThetaFinitePacketLogVolume.tupleWeight_pos D p j c).le
    (packet D p j c).saturatedLogShell_normalizationLogVolume_nonneg

theorem hull_packetLogVolume_le (p : Nat.Primes) (j : ℕ) :
    IutInitialThetaFinitePacketHull.packetLogVolume D p j ≤ packetLogVolume D p j := by
  apply Finset.sum_le_sum
  intro c _
  apply mul_le_mul_of_nonneg_left _ (IutInitialThetaFinitePacketLogVolume.tupleWeight_pos D p j c).le
  exact (packet D p j c).normalizationLogVolume_mono
    ((IutInitialThetaFinitePacketHull.componentHull_subset_normalization D p j c).trans
      (packet D p j c).normalization_subset_saturatedLogShell)
    (IutInitialThetaFinitePacketHull.componentHull_haar_pos_lt_top D p j c).1
    (packet D p j c).saturatedLogShell_haar_pos_lt_top.2.ne

theorem source_packetLogVolume_le (p : Nat.Primes) (j : ℕ) :
    IutInitialThetaFinitePacketLogVolume.packetLogVolume D p j ≤ packetLogVolume D p j :=
  (IutInitialThetaFinitePacketHull.source_packetLogVolume_le D p j).trans
    (hull_packetLogVolume_le D p j)

end
end JoshiTeich.Act1Scene1.IutInitialThetaFinitePacketLogShell
