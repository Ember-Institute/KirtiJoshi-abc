import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFiniteGlobalLowerBound
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorNormalizationHull

/-!
source-id: JT-SCENE1-INITIAL-THETA-FINITE-PACKET-HULL
source: Joshi III principal hull (3568--3574), le:volume-lemma3;
reference LocalConstruct/Hull, exists_leastHull_finite, and Concrete/Container,
hull, for componentwise least hulls and their packet product.
fidelity: constructs least principal normalization hulls of the actual
q-root factor orbits, identifies them with normalization-module spans,
and proves product leastness, compactness, positive finite Haar and finite
support. Transfers the proved q-pilot log-volume bounds to these actual
hulls with the original tuple weights. No paper theta-locus, integral-hull
or representative-weight identity is assumed. Original consumer proofs.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.IutInitialThetaFinitePacketHull

open JoshiTeich.Prologue MeasureTheory
open IutInitialThetaFinitePacketRegion
open scoped BigOperators Classical

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.property⟩
local instance fiberFinite (p : Nat.Primes) : Finite (Fiber D p) := Arithmetic.fiber_finite (p : ℕ)
local instance fiberFintype (p : Nat.Primes) : Fintype (Fiber D p) := Fintype.ofFinite _

def componentHull (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    Set (packet D p j c).Tensor :=
  (packet D p j c).leastHull
    (IutInitialThetaFiniteFactorRegion.region D (packet D p j c) (Fin.last j) j)
    (IutInitialThetaFiniteFactorRegion.region_isCompact D _ _ _).isBounded
    (IutInitialThetaFiniteFactorRegion.region_haar_pos_lt_top D _ _ _).1

theorem component_subset_hull (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    IutInitialThetaFiniteFactorRegion.region D (packet D p j c) (Fin.last j) j ⊆
      componentHull D p j c := (packet D p j c).subset_leastHull _ _ _

theorem componentHull_isCompact (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    IsCompact (componentHull D p j c) := (packet D p j c).leastHull_isCompact _ _ _

theorem componentHull_haar_pos_lt_top (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    0 < (packet D p j c).normalizationHaar (componentHull D p j c) ∧
      (packet D p j c).normalizationHaar (componentHull D p j c) < ⊤ :=
  (packet D p j c).leastHull_haar_pos_lt_top _ _ _

theorem componentHull_eq_normalizationHull (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    componentHull D p j c =
      ((packet D p j c).normalizationHull
        (IutInitialThetaFiniteFactorRegion.region D (packet D p j c) (Fin.last j) j) : Set _) :=
  ((packet D p j c).normalizationHull_eq_leastHull _ _ _).symm

theorem componentHull_isPrincipal (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    ∃ a : (packet D p j c).Tensor, IsUnit a ∧
      componentHull D p j c = (packet D p j c).principalRegion a :=
  ⟨_, (packet D p j c).hullMultiplier_isUnit _ _ _, rfl⟩

theorem componentHull_le_principalRegion (p : Nat.Primes) (j : ℕ) (c : Tuple D p j)
    (a : (packet D p j c).Tensor) (ha : IsUnit a)
    (hUa : IutInitialThetaFiniteFactorRegion.region D (packet D p j c) (Fin.last j) j ⊆
      (packet D p j c).principalRegion a) :
    componentHull D p j c ⊆ (packet D p j c).principalRegion a :=
  (packet D p j c).leastHull_le_principalRegion _ _ _ a ha hUa

theorem componentHull_subset_normalization (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    componentHull D p j c ⊆ (packet D p j c).normalization := by
  rw [componentHull_eq_normalizationHull]
  exact (packet D p j c).normalizationHull_subset_normalization _
    (IutInitialThetaFiniteFactorRegion.region_subset_normalization D _ _ _)

theorem componentHull_eq_normalization_of_not_bad (p : Nat.Primes) (j : ℕ)
    (c : Tuple D p j) (hp : (p : ℕ) ∉ IutInitialThetaQRootFamily.badChars D) :
    componentHull D p j c = ((packet D p j c).normalization : Set _) := by
  apply Set.Subset.antisymm (componentHull_subset_normalization D p j c)
  rw [← IutInitialThetaFiniteFactorRegion.region_eq_normalization_of_not_bad D _ _ _ hp]
  exact component_subset_hull D p j c

def region (p : Nat.Primes) (j : ℕ) : Set (Total D p j) :=
  Set.pi Set.univ (componentHull D p j)

theorem mem_region (p : Nat.Primes) (j : ℕ) (x : Total D p j) :
    x ∈ region D p j ↔ ∀ c, x c ∈ componentHull D p j c := by
  simp only [region, Set.mem_pi, Set.mem_univ, forall_const]

theorem source_subset_region (p : Nat.Primes) (j : ℕ) :
    IutInitialThetaFinitePacketRegion.region D p j ⊆ region D p j := by
  intro x hx
  exact (mem_region D p j x).mpr fun c => component_subset_hull D p j c
    ((IutInitialThetaFinitePacketRegion.mem_region D p j x).mp hx c)

theorem region_le_principal_product (p : Nat.Primes) (j : ℕ)
    (a : ∀ c : Tuple D p j, (packet D p j c).Tensor) (ha : ∀ c, IsUnit (a c))
    (hUa : IutInitialThetaFinitePacketRegion.region D p j ⊆
      Set.pi Set.univ (fun c => (packet D p j c).principalRegion (a c))) :
    region D p j ⊆ Set.pi Set.univ (fun c => (packet D p j c).principalRegion (a c)) := by
  have hcoord := Set.pi_subset_pi_iff.mp hUa
  have hUa' : ∀ c : Tuple D p j,
      IutInitialThetaFiniteFactorRegion.region D (packet D p j c) (Fin.last j) j ⊆
        (packet D p j c).principalRegion (a c) := by
    rcases hcoord with h | h
    · exact fun c => h c (Set.mem_univ c)
    · exact False.elim ((IutInitialThetaFinitePacketRegion.region_nonempty D p j).ne_empty h)
  exact Set.pi_mono fun c _ => componentHull_le_principalRegion D p j c (a c) (ha c) (hUa' c)

theorem region_isCompact (p : Nat.Primes) (j : ℕ) : IsCompact (region D p j) :=
  isCompact_univ_pi fun c => componentHull_isCompact D p j c

theorem region_subset_integralRegion (p : Nat.Primes) (j : ℕ) :
    region D p j ⊆ integralRegion D p j :=
  Set.pi_mono fun c _ => componentHull_subset_normalization D p j c

theorem productMeasure_region (p : Nat.Primes) (j : ℕ) :
    productMeasure D p j (region D p j) =
      ∏ c : Tuple D p j, (packet D p j c).normalizationHaar (componentHull D p j c) :=
  Measure.pi_pi _ _

theorem productMeasure_region_pos_lt_top (p : Nat.Primes) (j : ℕ) :
    0 < productMeasure D p j (region D p j) ∧ productMeasure D p j (region D p j) < ⊤ := by
  rw [productMeasure_region]
  exact ⟨bot_lt_iff_ne_bot.mpr (Finset.prod_ne_zero_iff.mpr
    fun c _ => (componentHull_haar_pos_lt_top D p j c).1.ne'),
    ENNReal.prod_lt_top fun c _ => (componentHull_haar_pos_lt_top D p j c).2⟩

theorem region_eq_integralRegion_of_not_bad (p : Nat.Primes) (j : ℕ)
    (hp : (p : ℕ) ∉ IutInitialThetaQRootFamily.badChars D) :
    region D p j = integralRegion D p j := by
  unfold region integralRegion
  congr 1
  funext c
  exact componentHull_eq_normalization_of_not_bad D p j c hp

def packetLogVolume (p : Nat.Primes) (j : ℕ) : ℝ := ∑ c : Tuple D p j,
  IutInitialThetaFinitePacketLogVolume.tupleWeight D p j c *
    IutInitialThetaFinitePacketLogVolume.componentLogVolume D p j c (componentHull D p j c)

theorem source_packetLogVolume_le (p : Nat.Primes) (j : ℕ) :
    IutInitialThetaFinitePacketLogVolume.packetLogVolume D p j ≤ packetLogVolume D p j := by
  apply Finset.sum_le_sum
  intro c _
  apply mul_le_mul_of_nonneg_left _ (IutInitialThetaFinitePacketLogVolume.tupleWeight_pos D p j c).le
  exact (packet D p j c).normalizationLogVolume_mono (component_subset_hull D p j c)
    (IutInitialThetaFiniteFactorRegion.region_haar_pos_lt_top D _ _ _).1
    (componentHull_haar_pos_lt_top D p j c).2.ne

theorem packetLogVolume_nonpos (p : Nat.Primes) (j : ℕ) : packetLogVolume D p j ≤ 0 := by
  apply Finset.sum_nonpos
  intro c _
  apply mul_nonpos_of_nonneg_of_nonpos
    (IutInitialThetaFinitePacketLogVolume.tupleWeight_pos D p j c).le
  have h := (packet D p j c).normalizationLogVolume_mono
    (componentHull_subset_normalization D p j c) (componentHull_haar_pos_lt_top D p j c).1
    (by rw [(packet D p j c).normalizationHaar_normalization]; exact ENNReal.one_ne_top)
  have hz := IutInitialThetaFinitePacketLogVolume.componentLogVolume_integral D p j c
  exact h.trans_eq hz

theorem packetLogVolume_bounds (p : Nat.Primes) (j : ℕ) :
    -((j ^ 2 : ℕ) : ℝ) * Real.log (p : ℕ) *
      IutInitialThetaQRootFamily.vbadWeightedFiber D (p : ℕ) ≤ packetLogVolume D p j ∧
      packetLogVolume D p j ≤ 0 :=
  ⟨(IutInitialThetaFinitePacketLowerBound.packetLogVolume_lower_bound D p j).trans
    (source_packetLogVolume_le D p j), packetLogVolume_nonpos D p j⟩

theorem packetLogVolume_eq_zero_of_not_bad (p : Nat.Primes) (j : ℕ)
    (hp : (p : ℕ) ∉ IutInitialThetaQRootFamily.badChars D) : packetLogVolume D p j = 0 :=
  le_antisymm (packetLogVolume_nonpos D p j)
    ((IutInitialThetaFinitePacketLogVolume.packetLogVolume_eq_zero_of_not_bad D p j hp) ▸
      source_packetLogVolume_le D p j)

end
end JoshiTeich.Act1Scene1.IutInitialThetaFinitePacketHull
