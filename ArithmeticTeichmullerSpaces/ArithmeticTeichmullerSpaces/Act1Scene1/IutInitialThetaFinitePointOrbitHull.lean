import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorPointOrbitHull
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaAdelicFamilyLogVolume

/-!
source-id: JT-SCENE1-INITIAL-THETA-FINITE-POINT-ORBIT-HULL
source: Joshi III principal hull, le:volume-lemma3, and the single-point
witness construction; reference ThetaRegion scaleElt / thetaFinite and
Cor312/RightHandSide's images-to-hull composition.
fidelity: the actual distinguished q-root point at every finite tuple,
its finite factor-automorphism orbit, and its normalization-generated hull.
The hull is exactly the previously constructed actual packet hull; its
weighted log-volume and finite support follow on the same carrier. Raw
points have zero Haar; positivity is proved only after taking their hull.
Original consumer proofs; no reference source code copied.
boundary: Scene1/Derived; no paper theta or full Ind1--Ind3 identification.
-/

namespace JoshiTeich.Act1Scene1.IutInitialThetaFinitePointOrbitHull

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
local instance integralModule (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    Module ℤ_[(p : ℕ)] (packet D p j c).Tensor :=
  Module.compHom _ (algebraMap ℤ_[(p : ℕ)] ℚ_[(p : ℕ)])

def componentPoints (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    Set (packet D p j c).Tensor :=
  (packet D p j c).factorPointOrbit
    (IutInitialThetaFiniteFactorRegion.scaleElt D (packet D p j c) (Fin.last j) j)

theorem scaleElt_mem_componentPoints (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    IutInitialThetaFiniteFactorRegion.scaleElt D (packet D p j c) (Fin.last j) j ∈
      componentPoints D p j c := (packet D p j c).mem_factorPointOrbit _

theorem componentPoints_finite (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    (componentPoints D p j c).Finite := (packet D p j c).factorPointOrbit_finite _

theorem componentPoints_isCompact (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    IsCompact (componentPoints D p j c) := (componentPoints_finite D p j c).isCompact

theorem componentPoints_haar_eq_zero (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    (packet D p j c).normalizationHaar (componentPoints D p j c) = 0 :=
  (packet D p j c).factorPointOrbit_haar_eq_zero _

theorem componentPoints_subset_source (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    componentPoints D p j c ⊆
      IutInitialThetaFiniteFactorRegion.region D (packet D p j c) (Fin.last j) j := by
  rw [IutInitialThetaFiniteFactorRegion.region_eq_orbit_principalRegion]
  exact (packet D p j c).factorPointOrbit_subset_thickOrbit _

def componentHull (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    Submodule (packet D p j c).normalization (packet D p j c).Tensor :=
  (packet D p j c).normalizationHull (componentPoints D p j c)

theorem componentHull_eq_existing (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    (componentHull D p j c : Set _) = IutInitialThetaFinitePacketHull.componentHull D p j c :=
  (packet D p j c).normalizationHull_purePointOrbit_eq_leastHull
    (IutInitialThetaFiniteFactorRegion.scalars D (packet D p j c) (Fin.last j) j)
    (IutInitialThetaFiniteFactorRegion.scalars_ne_zero D (packet D p j c) (Fin.last j) j)

theorem componentPoints_subset_hull (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    componentPoints D p j c ⊆ componentHull D p j c :=
  (packet D p j c).subset_normalizationHull _

theorem componentHull_isCompact (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    IsCompact (componentHull D p j c : Set (packet D p j c).Tensor) := by
  rw [componentHull_eq_existing]
  exact IutInitialThetaFinitePacketHull.componentHull_isCompact D p j c

theorem componentHull_haar_pos_lt_top (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    0 < (packet D p j c).normalizationHaar (componentHull D p j c) ∧
      (packet D p j c).normalizationHaar (componentHull D p j c) < ⊤ := by
  rw [componentHull_eq_existing]
  exact IutInitialThetaFinitePacketHull.componentHull_haar_pos_lt_top D p j c

theorem componentHull_le_principalRegion_iff (p : Nat.Primes) (j : ℕ) (c : Tuple D p j)
    (a : (packet D p j c).Tensor) :
    (componentHull D p j c : Set _) ⊆ (packet D p j c).principalRegion a ↔
      componentPoints D p j c ⊆ (packet D p j c).principalRegion a :=
  (packet D p j c).normalizationHull_pointOrbit_le_iff _ a

def pointRegion (p : Nat.Primes) (j : ℕ) : Set (Total D p j) :=
  Set.pi Set.univ (componentPoints D p j)

theorem pointRegion_isCompact (p : Nat.Primes) (j : ℕ) : IsCompact (pointRegion D p j) :=
  isCompact_univ_pi fun c => componentPoints_isCompact D p j c

theorem witness_mem_pointRegion (p : Nat.Primes) (j : ℕ) : witness D p j ∈ pointRegion D p j :=
  Set.mem_pi.mpr fun c _ => scaleElt_mem_componentPoints D p j c

theorem pointRegion_nonempty (p : Nat.Primes) (j : ℕ) : (pointRegion D p j).Nonempty :=
  ⟨witness D p j, witness_mem_pointRegion D p j⟩

theorem productMeasure_pointRegion_eq_zero (p : Nat.Primes) (j : ℕ) :
    productMeasure D p j (pointRegion D p j) = 0 := by
  have hprod : productMeasure D p j (pointRegion D p j) =
      ∏ c : Tuple D p j, (packet D p j c).normalizationHaar (componentPoints D p j c) :=
    Measure.pi_pi _ _
  rw [hprod]
  obtain ⟨c⟩ := tuple_nonempty D p j
  exact Finset.prod_eq_zero (Finset.mem_univ c) (componentPoints_haar_eq_zero D p j c)

def hullRegion (p : Nat.Primes) (j : ℕ) : Set (Total D p j) :=
  Set.pi Set.univ fun c => (componentHull D p j c : Set _)

theorem hullRegion_eq_existing (p : Nat.Primes) (j : ℕ) :
    hullRegion D p j = IutInitialThetaFinitePacketHull.region D p j := by
  unfold hullRegion IutInitialThetaFinitePacketHull.region
  congr 1
  funext c
  exact componentHull_eq_existing D p j c

theorem pointRegion_subset_hull (p : Nat.Primes) (j : ℕ) :
    pointRegion D p j ⊆ hullRegion D p j :=
  Set.pi_mono fun c _ => componentPoints_subset_hull D p j c

/-- Minimality uses containment of the point orbit, with no raw Haar hypothesis. -/
theorem hullRegion_le_principalProduct (p : Nat.Primes) (j : ℕ)
    (a : ∀ c : Tuple D p j, (packet D p j c).Tensor)
    (hU : pointRegion D p j ⊆ Set.pi Set.univ fun c => (packet D p j c).principalRegion (a c)) :
    hullRegion D p j ⊆ Set.pi Set.univ fun c => (packet D p j c).principalRegion (a c) := by
  rcases Set.pi_subset_pi_iff.mp hU with h | h
  · exact Set.pi_mono fun c _ => (componentHull_le_principalRegion_iff D p j c (a c)).mpr
      (h c (Set.mem_univ c))
  · exact False.elim ((pointRegion_nonempty D p j).ne_empty h)

theorem hullRegion_eq_integral_of_not_bad (p : Nat.Primes) (j : ℕ)
    (hp : (p : ℕ) ∉ IutInitialThetaQRootFamily.badChars D) :
    hullRegion D p j = integralRegion D p j := by
  rw [hullRegion_eq_existing]
  exact IutInitialThetaFinitePacketHull.region_eq_integralRegion_of_not_bad D p j hp

theorem hullRegion_finite_support (j : ℕ) :
    {p : Nat.Primes | hullRegion D p j ≠ integralRegion D p j}.Finite := by
  apply (badPrimes_finite D).subset
  intro p hp
  by_contra he
  exact hp (hullRegion_eq_integral_of_not_bad D p j he)

def packetHullLogVolume (p : Nat.Primes) (j : ℕ) : ℝ := ∑ c : Tuple D p j,
  IutInitialThetaFinitePacketLogVolume.tupleWeight D p j c *
    IutInitialThetaFinitePacketLogVolume.componentLogVolume D p j c (componentHull D p j c)

theorem packetHullLogVolume_eq_existing (p : Nat.Primes) (j : ℕ) :
    packetHullLogVolume D p j = IutInitialThetaFinitePacketHull.packetLogVolume D p j := by
  simp only [packetHullLogVolume, componentHull_eq_existing,
    IutInitialThetaFinitePacketHull.packetLogVolume]

theorem packetHullLogVolume_eq_productMeasure_log (p : Nat.Primes) (j : ℕ) :
    packetHullLogVolume D p j = Real.log (productMeasure D p j (hullRegion D p j)).toReal /
      (Module.finrank ℚ ↥D.prime.torsionField : ℝ) ^ (j + 1) := by
  rw [packetHullLogVolume_eq_existing, hullRegion_eq_existing]
  exact IutInitialThetaAdelicPacketHull.finite_packetLogVolume_eq_productMeasure_log D p j


/-- Replace the finite branches by point-generated hulls; retain the actual infinite hull. -/
def hullPacketFamily (j : ℕ) : IutInitialThetaAdelicHullClosure.Family D j
  | .finite p => fun c => ⟨componentHull D p j c, (componentHull_isCompact D p j c).isBounded,
      (componentHull_haar_pos_lt_top D p j c).1⟩
  | .infinite => IutInitialThetaAdelicHullClosure.adelicClosure D j
      (IutInitialThetaAdelicHullClosure.sourceFamily D j) .infinite

theorem hullPacketFamily_eq_existing (j : ℕ) :
    hullPacketFamily D j = IutInitialThetaAdelicHullClosure.adelicClosure D j
      (IutInitialThetaAdelicHullClosure.sourceFamily D j) := by
  funext vQ
  cases vQ with
  | finite p =>
    funext c
    apply Subtype.ext
    exact componentHull_eq_existing D p j c
  | infinite => rfl

def hullAdmissibleFamily (j : ℕ) : IutInitialThetaAdelicFamilyLogVolume.AdmissibleFamily D j :=
  ⟨hullPacketFamily D j, by
    rw [hullPacketFamily_eq_existing]
    exact IutInitialThetaAdelicHullClosure.closure_sourceFamily_finite_support D j⟩

theorem hullAdmissibleFamily_eq_existing (j : ℕ) :
    hullAdmissibleFamily D j = IutInitialThetaAdelicFamilyLogVolume.closureFamily D j
      (IutInitialThetaAdelicFamilyLogVolume.sourceAdmissibleFamily D j) :=
  Subtype.ext (hullPacketFamily_eq_existing D j)

theorem globalHullLogVolume_eq_existing (j : ℕ) :
    IutInitialThetaAdelicFamilyLogVolume.globalLogVolume D j (hullAdmissibleFamily D j) =
      IutInitialThetaAdelicPacketHull.globalLogVolume D j := by
  rw [hullAdmissibleFamily_eq_existing]
  exact IutInitialThetaAdelicFamilyLogVolume.globalLogVolume_hull D j

theorem processionHullLogVolume_eq_existing :
    IutInitialThetaAdelicFamilyLogVolume.processionLogVolume D
      (fun i => hullAdmissibleFamily D (i.val + 1)) =
        IutInitialThetaAdelicPacketHull.processionLogVolume D := by
  simp only [hullAdmissibleFamily_eq_existing,
    IutInitialThetaAdelicFamilyLogVolume.processionLogVolume_hull]

end
end JoshiTeich.Act1Scene1.IutInitialThetaFinitePointOrbitHull
