import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFinitePacketRegion
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Finprod

/-!
source-id: JT-SCENE1-INITIAL-THETA-FINITE-PACKET-LOG-VOLUME
source: `refer/iut/Iut/Concrete/Container.lean`, `weight`, `tupleWeight`,
`vol`; `LocalConstruct/Volume.lean`, `componentVol` (195--204);
`Cor312/LogVolume.lean`, `globalVol`, `processionVol`.
Joshi III `ss:weighted-vol` supplies the comparison target; the identity
with its representative-place weights remains a separate obligation.
fidelity: actual local-degree weights sum to one, as do all tuple weights.
The tensor dimension cancels the tuple degree product, relating the weighted
packet log-volume to the ordinary product measure already constructed.
Finite support makes the prime sum finite; the standard procession average
uses the same InitialThetaData and its positive ellStar. No paper theta,
BK, archimedean or final volume identity is assumed or asserted.
Original consumer proofs; no reference source code copied.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.IutInitialThetaFinitePacketLogVolume

open JoshiTeich.Prologue MeasureTheory IutInitialThetaFinitePacketRegion
open scoped BigOperators Classical

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.property⟩
local instance fiberFinite (p : Nat.Primes) : Finite (Fiber D p) :=
  Arithmetic.fiber_finite (p : ℕ)
local instance fiberFintype (p : Nat.Primes) : Fintype (Fiber D p) := Fintype.ofFinite _
local instance factorAlgebra (p : Nat.Primes) (j : ℕ) (c : Tuple D p j)
    (i : Fin (j + 1)) : Algebra ℚ_[(p : ℕ)] ((packet D p j c).Factor i) :=
  LocalCompletion.padicAlgebra ((packet D p j c).residueChar_eq i)

def placeWeight (p : Nat.Primes) (v : Fiber D p) : ℝ := Arithmetic.placeWeight v.1

theorem placeWeight_pos (p : Nat.Primes) (v : Fiber D p) : 0 < placeWeight D p v :=
  Arithmetic.placeWeight_pos v.1

theorem placeWeight_sum_one (p : Nat.Primes) : ∑ v : Fiber D p, placeWeight D p v = 1 := by
  simp only [placeWeight, Arithmetic.placeWeight, ← Finset.sum_div]
  rw [← Nat.cast_sum, Arithmetic.sum_localDeg (p : ℕ) p.property]
  exact div_self (Arithmetic.finrank_pos (K := ↥D.prime.torsionField)).ne'

def tupleWeight (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) : ℝ :=
  ∏ i, placeWeight D p (c i)

theorem tupleWeight_pos (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    0 < tupleWeight D p j c :=
  Finset.prod_pos fun i _ => placeWeight_pos D p (c i)

theorem tupleWeight_sum_one (p : Nat.Primes) (j : ℕ) :
    ∑ c : Tuple D p j, tupleWeight D p j c = 1 := by
  rw [show (fun c => tupleWeight D p j c) =
      (fun c : Tuple D p j => ∏ i, placeWeight D p (c i)) from rfl,
    ← Fintype.prod_sum]
  simp only [placeWeight_sum_one, Finset.prod_const_one]

theorem tupleWeight_le_one (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    tupleWeight D p j c ≤ 1 := by
  rw [← tupleWeight_sum_one D p j]
  exact Finset.single_le_sum (fun c _ => (tupleWeight_pos D p j c).le) (Finset.mem_univ c)

theorem tupleWeight_eq_dimension_div_degree (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    tupleWeight D p j c =
      (Module.finrank ℚ_[(p : ℕ)] (packet D p j c).Tensor : ℝ) /
        (Module.finrank ℚ ↥D.prime.torsionField : ℝ) ^ (j + 1) := by
  rw [(packet D p j c).tensor_finrank_eq_localDeg_prod]
  simp only [tupleWeight, placeWeight, Arithmetic.placeWeight,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Nat.cast_prod]
  rfl

def componentLogVolume (p : Nat.Primes) (j : ℕ) (c : Tuple D p j)
    (S : Set (packet D p j c).Tensor) : ℝ :=
  Real.log ((packet D p j c).normalizationHaar S).toReal /
    (Module.finrank ℚ_[(p : ℕ)] (packet D p j c).Tensor : ℝ)

theorem componentLogVolume_integral (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    componentLogVolume D p j c (packet D p j c).normalization = 0 := by
  simp [componentLogVolume, LocalCompletion.Packet.normalizationHaar_normalization]

theorem weighted_componentLogVolume (p : Nat.Primes) (j : ℕ) (c : Tuple D p j)
    (S : Set (packet D p j c).Tensor) :
    tupleWeight D p j c * componentLogVolume D p j c S =
      Real.log ((packet D p j c).normalizationHaar S).toReal /
        (Module.finrank ℚ ↥D.prime.torsionField : ℝ) ^ (j + 1) := by
  have hd : (Module.finrank ℚ_[(p : ℕ)] (packet D p j c).Tensor : ℝ) ≠ 0 := by
    exact_mod_cast (packet D p j c).tensor_finrank_pos.ne'
  rw [tupleWeight_eq_dimension_div_degree, componentLogVolume]
  field_simp

def packetLogVolume (p : Nat.Primes) (j : ℕ) : ℝ :=
  ∑ c : Tuple D p j, tupleWeight D p j c * componentLogVolume D p j c
    (IutInitialThetaFiniteFactorRegion.region D (packet D p j c) (Fin.last j) j)

theorem packetLogVolume_eq_sum_log_div_degree (p : Nat.Primes) (j : ℕ) :
    packetLogVolume D p j =
      (∑ c : Tuple D p j, Real.log ((packet D p j c).normalizationHaar
        (IutInitialThetaFiniteFactorRegion.region D (packet D p j c) (Fin.last j) j)).toReal) /
          (Module.finrank ℚ ↥D.prime.torsionField : ℝ) ^ (j + 1) := by
  simp only [packetLogVolume, weighted_componentLogVolume, Finset.sum_div]

theorem packetLogVolume_eq_productMeasure_log (p : Nat.Primes) (j : ℕ) :
    packetLogVolume D p j =
      Real.log (productMeasure D p j (region D p j)).toReal /
        (Module.finrank ℚ ↥D.prime.torsionField : ℝ) ^ (j + 1) := by
  rw [packetLogVolume_eq_sum_log_div_degree, productMeasure_region,
    ENNReal.toReal_prod, Real.log_prod]
  intro c _
  exact (ENNReal.toReal_pos
    (IutInitialThetaFiniteFactorRegion.region_haar_pos_lt_top D _ _ _).1.ne'
    (IutInitialThetaFiniteFactorRegion.region_haar_pos_lt_top D _ _ _).2.ne).ne'

theorem packetLogVolume_nonpos (p : Nat.Primes) (j : ℕ) : packetLogVolume D p j ≤ 0 := by
  rw [packetLogVolume_eq_productMeasure_log]
  have hm : (productMeasure D p j (region D p j)).toReal ≤ 1 := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_mono ENNReal.one_ne_top (productMeasure_region_le_one D p j))
  exact div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos ENNReal.toReal_nonneg hm)
    (pow_nonneg (Arithmetic.finrank_pos (K := ↥D.prime.torsionField)).le _)

theorem packetLogVolume_eq_zero_of_not_bad (p : Nat.Primes) (j : ℕ)
    (hp : (p : ℕ) ∉ IutInitialThetaQRootFamily.badChars D) :
    packetLogVolume D p j = 0 := by
  rw [packetLogVolume_eq_productMeasure_log,
    region_eq_integralRegion_of_not_bad D p j hp, productMeasure_integralRegion]
  simp

def badPrimes : Finset Nat.Primes := (badPrimes_finite D).toFinset

theorem mem_badPrimes (p : Nat.Primes) :
    p ∈ badPrimes D ↔ (p : ℕ) ∈ IutInitialThetaQRootFamily.badChars D := by
  simp [badPrimes]

theorem packetLogVolume_support_subset (j : ℕ) :
    Function.support (fun p => packetLogVolume D p j) ⊆ (badPrimes D : Set Nat.Primes) := by
  intro p hp
  by_contra hb
  exact hp (packetLogVolume_eq_zero_of_not_bad D p j (by simpa [mem_badPrimes] using hb))

theorem packetLogVolume_finite_support (j : ℕ) :
    (Function.support fun p => packetLogVolume D p j).Finite :=
  (badPrimes D).finite_toSet.subset (packetLogVolume_support_subset D j)

def globalLogVolume (j : ℕ) : ℝ := ∑ᶠ p : Nat.Primes, packetLogVolume D p j

theorem globalLogVolume_eq_sum (j : ℕ) :
    globalLogVolume D j = ∑ p ∈ badPrimes D, packetLogVolume D p j :=
  finsum_eq_sum_of_support_subset _ (packetLogVolume_support_subset D j)

theorem globalLogVolume_nonpos (j : ℕ) : globalLogVolume D j ≤ 0 := by
  rw [globalLogVolume_eq_sum]
  exact Finset.sum_nonpos fun p _ => packetLogVolume_nonpos D p j

def processionLogVolume : ℝ :=
  (∑ i : Index D, globalLogVolume D (i.val + 1)) / (((D.prime.ℓ - 1) / 2 : ℕ) : ℝ)

theorem processionLogVolume_eq_sum :
    processionLogVolume D =
      (∑ i : Index D, ∑ p ∈ badPrimes D, packetLogVolume D p (i.val + 1)) /
        (((D.prime.ℓ - 1) / 2 : ℕ) : ℝ) := by
  simp only [processionLogVolume, globalLogVolume_eq_sum]

theorem processionLogVolume_eq_prime_sum :
    processionLogVolume D =
      (∑ p ∈ badPrimes D, ∑ i : Index D, packetLogVolume D p (i.val + 1)) /
        (((D.prime.ℓ - 1) / 2 : ℕ) : ℝ) := by
  rw [processionLogVolume_eq_sum, Finset.sum_comm]

theorem processionLogVolume_nonpos : processionLogVolume D ≤ 0 := by
  unfold processionLogVolume
  exact div_nonpos_of_nonpos_of_nonneg
    (Finset.sum_nonpos fun i _ => globalLogVolume_nonpos D (i.val + 1)) (Nat.cast_nonneg _)

theorem negative_abs_processionLogVolume :
    -|processionLogVolume D| = processionLogVolume D := by
  rw [abs_of_nonpos (processionLogVolume_nonpos D), neg_neg]

end
end JoshiTeich.Act1Scene1.IutInitialThetaFinitePacketLogVolume
