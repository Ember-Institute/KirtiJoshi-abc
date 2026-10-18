import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorPrimeLogVolume
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFinitePacketLogShell

/-!
source-id: JT-SCENE1-INITIAL-THETA-FINITE-PACKET-PRIME-LOG-VOLUME
source: reference Cor312/LogVolume.componentVol_prime_preimage and
Concrete/Container tupleWeight / vol; IUT III Proposition 3.9(i).
fidelity: actual InitialThetaData, all finite-place tuples, actual Haar and
local-degree weights. Proves prime-preimage scaling for positive finite
measurable component families and consumes it on source, hull and shell.
Original consumer proofs; no reference source code copied.
boundary: Scene1/Derived; no selected paper weights or thetaVolume identity.
-/

namespace JoshiTeich.Act1Scene1.IutInitialThetaFinitePacketPrimeLogVolume

open JoshiTeich.Prologue MeasureTheory IutInitialThetaFinitePacketRegion
open IutInitialThetaFinitePacketLogVolume
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.property⟩
local instance fiberFinite (p : Nat.Primes) : Finite (Fiber D p) := Arithmetic.fiber_finite (p : ℕ)
local instance fiberFintype (p : Nat.Primes) : Fintype (Fiber D p) := Fintype.ofFinite _

/-- The same weighted packet functional on any family of actual component regions. -/
def familyLogVolume (p : Nat.Primes) (j : ℕ)
    (U : ∀ c : Tuple D p j, Set (packet D p j c).Tensor) : ℝ :=
  ∑ c, tupleWeight D p j c * componentLogVolume D p j c (U c)

def primePreimageFamily (p : Nat.Primes) (j : ℕ)
    (U : ∀ c : Tuple D p j, Set (packet D p j c).Tensor) :
    ∀ c : Tuple D p j, Set (packet D p j c).Tensor :=
  fun c => (packet D p j c).primePreimage (U c)

theorem familyLogVolume_eq_productMeasure_log (p : Nat.Primes) (j : ℕ)
    (U : ∀ c : Tuple D p j, Set (packet D p j c).Tensor)
    (hpos : ∀ c, 0 < (packet D p j c).normalizationHaar (U c))
    (hfin : ∀ c, (packet D p j c).normalizationHaar (U c) < ⊤) :
    familyLogVolume D p j U =
      Real.log (productMeasure D p j (Set.pi Set.univ U)).toReal /
        (Module.finrank ℚ ↥D.prime.torsionField : ℝ) ^ (j + 1) := by
  have hprod : productMeasure D p j (Set.pi Set.univ U) =
      ∏ c : Tuple D p j, (packet D p j c).normalizationHaar (U c) :=
    Measure.pi_pi _ _
  calc
    _ = (∑ c : Tuple D p j, Real.log ((packet D p j c).normalizationHaar (U c)).toReal) /
        (Module.finrank ℚ ↥D.prime.torsionField : ℝ) ^ (j + 1) := by
      simp only [familyLogVolume, weighted_componentLogVolume, Finset.sum_div]
    _ = _ := by
      rw [hprod, ENNReal.toReal_prod, Real.log_prod]
      intro c _
      exact (ENNReal.toReal_pos (hpos c).ne' (hfin c).ne).ne'

theorem componentLogVolume_primePreimage (p : Nat.Primes) (j : ℕ) (c : Tuple D p j)
    (U : Set (packet D p j c).Tensor) (hU : MeasurableSet U)
    (hpos : 0 < (packet D p j c).normalizationHaar U)
    (hfin : (packet D p j c).normalizationHaar U < ⊤) :
    componentLogVolume D p j c ((packet D p j c).primePreimage U) =
      componentLogVolume D p j c U + Real.log (p : ℕ) :=
  (packet D p j c).normalizationLogVolume_primePreimage hU hpos hfin

/-- The mass-one tuple weights make the packet shift exactly `log p`. -/
theorem familyLogVolume_primePreimage (p : Nat.Primes) (j : ℕ)
    (U : ∀ c : Tuple D p j, Set (packet D p j c).Tensor)
    (hU : ∀ c, MeasurableSet (U c))
    (hpos : ∀ c, 0 < (packet D p j c).normalizationHaar (U c))
    (hfin : ∀ c, (packet D p j c).normalizationHaar (U c) < ⊤) :
    familyLogVolume D p j (primePreimageFamily D p j U) =
      familyLogVolume D p j U + Real.log (p : ℕ) := by
  simp only [familyLogVolume, primePreimageFamily,
    componentLogVolume_primePreimage D p j _ _ (hU _) (hpos _) (hfin _),
    mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, tupleWeight_sum_one, one_mul]

theorem primePreimageFamily_haar_pos_lt_top (p : Nat.Primes) (j : ℕ)
    (U : ∀ c : Tuple D p j, Set (packet D p j c).Tensor)
    (hU : ∀ c, MeasurableSet (U c))
    (hpos : ∀ c, 0 < (packet D p j c).normalizationHaar (U c))
    (hfin : ∀ c, (packet D p j c).normalizationHaar (U c) < ⊤) :
    ∀ c, 0 < (packet D p j c).normalizationHaar (primePreimageFamily D p j U c) ∧
      (packet D p j c).normalizationHaar (primePreimageFamily D p j U c) < ⊤ :=
  fun c => (packet D p j c).primePreimage_haar_pos_lt_top (hU c) (hpos c) (hfin c)

/-- A statement on actual packet product Haar, with the same global-degree denominator. -/
theorem productMeasure_log_primePreimage (p : Nat.Primes) (j : ℕ)
    (U : ∀ c : Tuple D p j, Set (packet D p j c).Tensor)
    (hU : ∀ c, MeasurableSet (U c))
    (hpos : ∀ c, 0 < (packet D p j c).normalizationHaar (U c))
    (hfin : ∀ c, (packet D p j c).normalizationHaar (U c) < ⊤) :
    Real.log (productMeasure D p j (Set.pi Set.univ (primePreimageFamily D p j U))).toReal /
        (Module.finrank ℚ ↥D.prime.torsionField : ℝ) ^ (j + 1) =
      Real.log (productMeasure D p j (Set.pi Set.univ U)).toReal /
        (Module.finrank ℚ ↥D.prime.torsionField : ℝ) ^ (j + 1) + Real.log (p : ℕ) := by
  have hpre := primePreimageFamily_haar_pos_lt_top D p j U hU hpos hfin
  rw [← familyLogVolume_eq_productMeasure_log D p j _ (fun c => (hpre c).1)
    (fun c => (hpre c).2), ← familyLogVolume_eq_productMeasure_log D p j U hpos hfin]
  exact familyLogVolume_primePreimage D p j U hU hpos hfin

theorem source_primePreimage_logVolume (p : Nat.Primes) (j : ℕ) :
    familyLogVolume D p j (primePreimageFamily D p j (fun c =>
      IutInitialThetaFiniteFactorRegion.region D (packet D p j c) (Fin.last j) j)) =
        packetLogVolume D p j + Real.log (p : ℕ) := by
  apply familyLogVolume_primePreimage
  · exact fun c => (IutInitialThetaFiniteFactorRegion.region_isCompact D _ _ _).measurableSet
  · exact fun c => (IutInitialThetaFiniteFactorRegion.region_haar_pos_lt_top D _ _ _).1
  · exact fun c => (IutInitialThetaFiniteFactorRegion.region_haar_pos_lt_top D _ _ _).2

theorem hull_primePreimage_logVolume (p : Nat.Primes) (j : ℕ) :
    familyLogVolume D p j
      (primePreimageFamily D p j (IutInitialThetaFinitePacketHull.componentHull D p j)) =
        IutInitialThetaFinitePacketHull.packetLogVolume D p j + Real.log (p : ℕ) := by
  apply familyLogVolume_primePreimage
  · exact fun c => (IutInitialThetaFinitePacketHull.componentHull_isCompact D p j c).measurableSet
  · exact fun c => (IutInitialThetaFinitePacketHull.componentHull_haar_pos_lt_top D p j c).1
  · exact fun c => (IutInitialThetaFinitePacketHull.componentHull_haar_pos_lt_top D p j c).2

theorem shell_primePreimage_logVolume (p : Nat.Primes) (j : ℕ) :
    familyLogVolume D p j
      (primePreimageFamily D p j (IutInitialThetaFinitePacketLogShell.componentShell D p j)) =
        IutInitialThetaFinitePacketLogShell.packetLogVolume D p j + Real.log (p : ℕ) := by
  apply familyLogVolume_primePreimage
  · exact fun c => (packet D p j c).saturatedLogShell_isCompact.measurableSet
  · exact fun c => (packet D p j c).saturatedLogShell_haar_pos_lt_top.1
  · exact fun c => (packet D p j c).saturatedLogShell_haar_pos_lt_top.2

end
end JoshiTeich.Act1Scene1.IutInitialThetaFinitePacketPrimeLogVolume
