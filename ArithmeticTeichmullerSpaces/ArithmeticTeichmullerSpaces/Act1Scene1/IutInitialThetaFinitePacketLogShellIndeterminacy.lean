import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorLogShellIndeterminacy
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFinitePacketLogShell

/-!
source-id: JT-SCENE1-INITIAL-THETA-FINITE-PACKET-SHELL-INDETERMINACY
source: reference LocalConstruct/LogShell, indAut_logShell, and
Concrete/Container packet products; Joshi III tensor log-shell construction.
fidelity: for the same actual D, arbitrary completion-factor automorphisms
chosen independently on every tuple induce a bijective map of the actual
packet total preserving the whole saturated log-shell product. Also proves
the component factor orbit is exactly the constructed shell and transports
its compactness and positive finite Haar. No global finite support or paper
Ind1--Ind3/BK identity is asserted. Original consumer proofs.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.IutInitialThetaFinitePacketLogShellIndeterminacy

open JoshiTeich.Prologue MeasureTheory IutInitialThetaFinitePacketRegion
open scoped Classical
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

abbrev Automorphisms (p : Nat.Primes) (j : ℕ) :=
  ∀ (c : Tuple D p j) (i : Fin (j + 1)),
    (packet D p j c).Factor i ≃ₐ[ℚ_[(p : ℕ)]] (packet D p j c).Factor i

def packetMap (p : Nat.Primes) (j : ℕ) (σ : Automorphisms D p j) :
    Total D p j → Total D p j := fun x c => (packet D p j c).factorTensorAut (σ c) (x c)

theorem packetMap_inverse_family (p : Nat.Primes) (j : ℕ) (σ : Automorphisms D p j)
    (x : Total D p j) : packetMap D p j σ (packetMap D p j (fun c i => (σ c i).symm) x) = x := by
  funext c
  exact (packet D p j c).factorTensorAut_apply_inverse_family (σ c) (x c)

theorem packetMap_bijective (p : Nat.Primes) (j : ℕ) (σ : Automorphisms D p j) :
    Function.Bijective (packetMap D p j σ) := by
  constructor
  · intro x y h
    funext c
    exact ((packet D p j c).factorTensorAut (σ c)).injective (congrFun h c)
  · intro x
    exact ⟨packetMap D p j (fun c i => (σ c i).symm) x, packetMap_inverse_family D p j σ x⟩

theorem packetMap_mem_region (p : Nat.Primes) (j : ℕ) (σ : Automorphisms D p j)
    {x : Total D p j} (hx : x ∈ IutInitialThetaFinitePacketLogShell.region D p j) :
    packetMap D p j σ x ∈ IutInitialThetaFinitePacketLogShell.region D p j := by
  intro c hc
  exact (packet D p j c).factorTensorAut_mem_saturatedLogShell (σ c) (hx c hc)

theorem packetMap_image_region (p : Nat.Primes) (j : ℕ) (σ : Automorphisms D p j) :
    packetMap D p j σ '' IutInitialThetaFinitePacketLogShell.region D p j =
      IutInitialThetaFinitePacketLogShell.region D p j := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact packetMap_mem_region D p j σ hx
  · intro x hx
    exact ⟨packetMap D p j (fun c i => (σ c i).symm) x,
      packetMap_mem_region D p j _ hx, packetMap_inverse_family D p j σ x⟩

theorem componentOrbit_eq_shell (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    (packet D p j c).factorIndeterminacyOrbit
      (IutInitialThetaFinitePacketLogShell.componentShell D p j c) =
        IutInitialThetaFinitePacketLogShell.componentShell D p j c :=
  (packet D p j c).factorIndeterminacyOrbit_saturatedLogShell

theorem componentOrbit_isCompact (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    IsCompact ((packet D p j c).factorIndeterminacyOrbit
      (IutInitialThetaFinitePacketLogShell.componentShell D p j c)) := by
  rw [componentOrbit_eq_shell]
  exact (packet D p j c).saturatedLogShell_isCompact

theorem componentOrbit_haar_pos_lt_top (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    0 < (packet D p j c).normalizationHaar ((packet D p j c).factorIndeterminacyOrbit
        (IutInitialThetaFinitePacketLogShell.componentShell D p j c)) ∧
      (packet D p j c).normalizationHaar ((packet D p j c).factorIndeterminacyOrbit
        (IutInitialThetaFinitePacketLogShell.componentShell D p j c)) < ⊤ :=
  (packet D p j c).factorIndeterminacyOrbit_saturatedLogShell_haar_pos_lt_top

end
end JoshiTeich.Act1Scene1.IutInitialThetaFinitePacketLogShellIndeterminacy
