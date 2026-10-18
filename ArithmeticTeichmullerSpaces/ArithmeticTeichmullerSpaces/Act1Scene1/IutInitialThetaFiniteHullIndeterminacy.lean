import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorHullIndeterminacy
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFinitePointOrbitHull
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFinitePacketLogShellIndeterminacy

/-!
source-id: JT-SCENE1-INITIAL-THETA-FINITE-HULL-INDETERMINACY
source: reference LocalConstruct/Indeterminacy, Concrete/ThetaRegion and
Cor312/RightHandSide; Joshi III principal hull and indeterminacy discussion.
fidelity: arbitrary actual completion-factor automorphisms on every tuple
preserve the actual point orbit, thickened source and its principal hull.
Packet product Haar and weighted component log are invariant under images
on arbitrary product regions. No paper Ind1--Ind3 or theta-locus identity.
Original consumer proofs; no reference source code copied.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.IutInitialThetaFiniteHullIndeterminacy

open JoshiTeich.Prologue MeasureTheory IutInitialThetaFinitePacketRegion
open IutInitialThetaFinitePacketLogShellIndeterminacy
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.property⟩
local instance fiberFinite (p : Nat.Primes) : Finite (Fiber D p) := Arithmetic.fiber_finite (p : ℕ)
local instance fiberFintype (p : Nat.Primes) : Fintype (Fiber D p) := Fintype.ofFinite _
local instance factorAlgebra (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) (i : Fin (j + 1)) :
    Algebra ℚ_[(p : ℕ)] ((packet D p j c).Factor i) :=
  LocalCompletion.padicAlgebra ((packet D p j c).residueChar_eq i)

theorem componentPointOrbit_image (p : Nat.Primes) (j : ℕ) (σ : Automorphisms D p j)
    (c : Tuple D p j) :
    (packet D p j c).factorTensorAut (σ c) ''
      IutInitialThetaFinitePointOrbitHull.componentPoints D p j c =
        IutInitialThetaFinitePointOrbitHull.componentPoints D p j c :=
  (packet D p j c).factorTensorAut_image_orbit (σ c) _

theorem componentSource_image (p : Nat.Primes) (j : ℕ) (σ : Automorphisms D p j)
    (c : Tuple D p j) :
    (packet D p j c).factorTensorAut (σ c) ''
      IutInitialThetaFiniteFactorRegion.region D (packet D p j c) (Fin.last j) j =
        IutInitialThetaFiniteFactorRegion.region D (packet D p j c) (Fin.last j) j :=
  (packet D p j c).factorTensorAut_image_orbit (σ c) _

theorem componentHull_image (p : Nat.Primes) (j : ℕ) (σ : Automorphisms D p j)
    (c : Tuple D p j) :
    (packet D p j c).factorTensorAut (σ c) '' IutInitialThetaFinitePacketHull.componentHull D p j c =
      IutInitialThetaFinitePacketHull.componentHull D p j c := by
  rw [← IutInitialThetaFinitePointOrbitHull.componentHull_eq_existing]
  exact (packet D p j c).factorTensorAut_image_orbitHull (σ c) _

theorem componentHull_orbit_eq_self (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    (packet D p j c).factorIndeterminacyOrbit (IutInitialThetaFinitePacketHull.componentHull D p j c) =
      IutInitialThetaFinitePacketHull.componentHull D p j c := by
  rw [← IutInitialThetaFinitePointOrbitHull.componentHull_eq_existing]
  exact (packet D p j c).factorIndeterminacyOrbit_orbitHull _

/-- The map acts on each actual tuple component independently. -/
theorem packetMap_image_product (p : Nat.Primes) (j : ℕ) (σ : Automorphisms D p j)
    (U : ∀ c : Tuple D p j, Set (packet D p j c).Tensor) :
    packetMap D p j σ '' Set.pi Set.univ U =
      Set.pi Set.univ (fun c => (packet D p j c).factorTensorAut (σ c) '' U c) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩ c _
    exact ⟨x c, hx c (Set.mem_univ c), rfl⟩
  · intro x hx
    choose y hy he using fun c => hx c (Set.mem_univ c)
    exact ⟨y, Set.mem_pi.mpr fun c _ => hy c, funext he⟩

theorem packetMap_image_pointRegion (p : Nat.Primes) (j : ℕ) (σ : Automorphisms D p j) :
    packetMap D p j σ '' IutInitialThetaFinitePointOrbitHull.pointRegion D p j =
      IutInitialThetaFinitePointOrbitHull.pointRegion D p j := by
  rw [IutInitialThetaFinitePointOrbitHull.pointRegion, packetMap_image_product]
  congr 1
  funext c
  exact componentPointOrbit_image D p j σ c

theorem packetMap_image_sourceRegion (p : Nat.Primes) (j : ℕ) (σ : Automorphisms D p j) :
    packetMap D p j σ '' region D p j = region D p j := by
  rw [region, packetMap_image_product]
  congr 1
  funext c
  exact componentSource_image D p j σ c

theorem packetMap_image_hullRegion (p : Nat.Primes) (j : ℕ) (σ : Automorphisms D p j) :
    packetMap D p j σ '' IutInitialThetaFinitePacketHull.region D p j =
      IutInitialThetaFinitePacketHull.region D p j := by
  rw [IutInitialThetaFinitePacketHull.region, packetMap_image_product]
  congr 1
  funext c
  exact componentHull_image D p j σ c

theorem productMeasure_packetMap_image_product (p : Nat.Primes) (j : ℕ)
    (σ : Automorphisms D p j) (U : ∀ c : Tuple D p j, Set (packet D p j c).Tensor) :
    productMeasure D p j (packetMap D p j σ '' Set.pi Set.univ U) =
      productMeasure D p j (Set.pi Set.univ U) := by
  rw [packetMap_image_product]
  have hleft : productMeasure D p j
      (Set.pi Set.univ (fun c => (packet D p j c).factorTensorAut (σ c) '' U c)) =
        ∏ c : Tuple D p j, (packet D p j c).normalizationHaar
          ((packet D p j c).factorTensorAut (σ c) '' U c) := Measure.pi_pi _ _
  have hright : productMeasure D p j (Set.pi Set.univ U) =
      ∏ c : Tuple D p j, (packet D p j c).normalizationHaar (U c) := Measure.pi_pi _ _
  rw [hleft, hright]
  apply Finset.prod_congr rfl
  intro c _
  exact (packet D p j c).normalizationHaar_factorTensorAut_image (σ c) (U c)

theorem weightedLogVolume_image_family (p : Nat.Primes) (j : ℕ) (σ : Automorphisms D p j)
    (U : ∀ c : Tuple D p j, Set (packet D p j c).Tensor) :
    IutInitialThetaFinitePacketPrimeLogVolume.familyLogVolume D p j
      (fun c => (packet D p j c).factorTensorAut (σ c) '' U c) =
        IutInitialThetaFinitePacketPrimeLogVolume.familyLogVolume D p j U := by
  unfold IutInitialThetaFinitePacketPrimeLogVolume.familyLogVolume
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  exact (packet D p j c).normalizationLogVolume_factorTensorAut_image (σ c) (U c)

/-- The ordinary product-Haar expression uses the same global-degree denominator. -/
theorem productLogVolume_packetMap_image (p : Nat.Primes) (j : ℕ)
    (σ : Automorphisms D p j) (U : ∀ c : Tuple D p j, Set (packet D p j c).Tensor) :
    Real.log (productMeasure D p j (packetMap D p j σ '' Set.pi Set.univ U)).toReal /
        (Module.finrank ℚ ↥D.prime.torsionField : ℝ) ^ (j + 1) =
      Real.log (productMeasure D p j (Set.pi Set.univ U)).toReal /
        (Module.finrank ℚ ↥D.prime.torsionField : ℝ) ^ (j + 1) := by
  rw [productMeasure_packetMap_image_product]

end
end JoshiTeich.Act1Scene1.IutInitialThetaFiniteHullIndeterminacy
