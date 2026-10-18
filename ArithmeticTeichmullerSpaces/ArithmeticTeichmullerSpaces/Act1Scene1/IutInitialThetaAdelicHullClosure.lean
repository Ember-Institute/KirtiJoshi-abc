import ArithmeticTeichmullerSpaces.Act1Scene1.LocalTensorHullClosure
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaArchimedeanPacketHull
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaAdelicLogShell

/-!
source-id: JT-SCENE1-INITIAL-THETA-ADELIC-HULL-CLOSURE
source: reference Concrete/Container, hull; Cor312/ContainerHull,
hullFamily, hull_integralRegion and hullAdmissible_idem.
fidelity: on all actual tuple components of the same D, constructs the
componentwise hull closure and its adelic family closure. Integral and
ordinary saturated log-shell families are fixed points. The actual source
family's closure is the previously constructed adelic packet hull. Proves
support preservation for every admissible family, without a hull-existence
certificate from the caller. Paper theta/RHSData identity remains separate.
Original consumer proofs; no reference code copied.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.IutInitialThetaAdelicHullClosure

open NumberField MeasureTheory IutInitialThetaAdelicPacketRegion
open JoshiTeich.Prologue
open scoped Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.property⟩
local instance fiberFinite (p : Nat.Primes) :
    Finite (IutInitialThetaFinitePacketRegion.Fiber D p) := Arithmetic.fiber_finite (p : ℕ)
local instance fiberFintype (p : Nat.Primes) :
    Fintype (IutInitialThetaFinitePacketRegion.Fiber D p) := Fintype.ofFinite _

def componentwiseClosure {C : Type*} {E : C → Type*} [∀ c, PartialOrder (E c)]
    (H : ∀ c, ClosureOperator (E c)) : ClosureOperator (∀ c, E c) where
  toFun U c := H c (U c)
  monotone' U V h c := (H c).monotone (h c)
  le_closure' U c := (H c).le_closure (U c)
  idempotent' U := funext fun c => (H c).idempotent (U c)

def PacketFamily (j : ℕ) : RationalPlace → Type u
  | .finite p => ∀ c : IutInitialThetaFinitePacketRegion.Tuple D p j,
      (IutInitialThetaFinitePacketRegion.packet D p j c).AdmissibleHullRegion
  | .infinite => ∀ c : IutInitialThetaArchimedeanPacketRegion.Tuple D j,
      LocalArchimedean.AdmissibleHullRegion c

instance packetFamilyPartialOrder (j : ℕ) (vQ : RationalPlace) : PartialOrder (PacketFamily D j vQ) := by
  cases vQ <;> unfold PacketFamily <;> infer_instance

def packetClosure (j : ℕ) : (vQ : RationalPlace) → ClosureOperator (PacketFamily D j vQ)
  | .finite p => componentwiseClosure fun c => (IutInitialThetaFinitePacketRegion.packet D p j c).hullClosure
  | .infinite => componentwiseClosure fun c => LocalArchimedean.hullClosure c

abbrev Family (j : ℕ) := ∀ vQ, PacketFamily D j vQ

def adelicClosure (j : ℕ) : ClosureOperator (Family D j) :=
  componentwiseClosure (packetClosure D j)

def productRegion (j : ℕ) : (vQ : RationalPlace) → PacketFamily D j vQ → Set (Total D j vQ)
  | .finite _, U => Set.pi Set.univ fun c => (U c).1
  | .infinite, U => Set.pi Set.univ fun c => (U c).1

theorem productRegion_mono (j : ℕ) (vQ : RationalPlace) {U V : PacketFamily D j vQ}
    (hUV : U ≤ V) : productRegion D j vQ U ⊆ productRegion D j vQ V := by
  cases vQ <;> exact Set.pi_mono (fun c _ => hUV c)

def integralFamily (j : ℕ) : Family D j
  | .finite p => fun c => (IutInitialThetaFinitePacketRegion.packet D p j c).integralHullRegion
  | .infinite => fun c => LocalArchimedean.integralHullRegion c

theorem packetClosure_integralFamily (j : ℕ) (vQ : RationalPlace) :
    packetClosure D j vQ (integralFamily D j vQ) = integralFamily D j vQ := by
  cases vQ with
  | finite p => funext c; exact (IutInitialThetaFinitePacketRegion.packet D p j c).hullClosure_integralHullRegion
  | infinite => funext c; exact LocalArchimedean.hullClosure_integralHullRegion c

theorem adelicClosure_integralFamily (j : ℕ) :
    adelicClosure D j (integralFamily D j) = integralFamily D j :=
  funext (packetClosure_integralFamily D j)

theorem productRegion_integralFamily (j : ℕ) (vQ : RationalPlace) :
    productRegion D j vQ (integralFamily D j vQ) = integralRegion D j vQ := by
  cases vQ <;> rfl

def shellFamily (j : ℕ) : Family D j
  | .finite p => fun c => (IutInitialThetaFinitePacketRegion.packet D p j c).saturatedShellHullRegion
  | .infinite => fun c => LocalArchimedean.logShellHullRegion c

theorem adelicClosure_shellFamily (j : ℕ) : adelicClosure D j (shellFamily D j) = shellFamily D j := by
  funext vQ
  cases vQ with
  | finite p => funext c; exact (IutInitialThetaFinitePacketRegion.packet D p j c).hullClosure_saturatedShellHullRegion
  | infinite => funext c; exact LocalArchimedean.hullClosure_logShellHullRegion c

theorem productRegion_shellFamily (j : ℕ) (vQ : RationalPlace) :
    productRegion D j vQ (shellFamily D j vQ) = IutInitialThetaAdelicLogShell.region D j vQ := by
  cases vQ with
  | finite p => rfl
  | infinite => exact (IutInitialThetaArchimedeanPacketRegion.region_eq_shell_product D j).symm

def sourceFamily (j : ℕ) : Family D j
  | .finite p => fun c =>
      ⟨IutInitialThetaFiniteFactorRegion.region D (IutInitialThetaFinitePacketRegion.packet D p j c) (Fin.last j) j,
        (IutInitialThetaFiniteFactorRegion.region_isCompact D _ _ _).isBounded,
        (IutInitialThetaFiniteFactorRegion.region_haar_pos_lt_top D _ _ _).1⟩
  | .infinite => fun c =>
      ⟨LocalArchimedean.factorOrbit c (LocalArchimedean.archLogShell c),
        (LocalArchimedean.isCompact_factorOrbit_archLogShell c).isBounded,
        (LocalArchimedean.factorOrbit_archLogShell_haar_pos_lt_top c).1⟩

theorem productRegion_sourceFamily (j : ℕ) (vQ : RationalPlace) :
    productRegion D j vQ (sourceFamily D j vQ) = IutInitialThetaAdelicPacketRegion.region D j vQ := by
  cases vQ <;> rfl

theorem productRegion_closure_sourceFamily (j : ℕ) (vQ : RationalPlace) :
    productRegion D j vQ (adelicClosure D j (sourceFamily D j) vQ) =
      IutInitialThetaAdelicPacketHull.region D j vQ := by
  cases vQ with
  | finite p => rfl
  | infinite =>
    change Set.pi Set.univ (IutInitialThetaArchimedeanPacketHull.componentHull D j) = _
    exact IutInitialThetaArchimedeanPacketHull.region_eq_source D j

theorem sourceFamily_le_shellFamily (j : ℕ) : sourceFamily D j ≤ shellFamily D j := by
  intro vQ
  cases vQ with
  | finite p =>
    intro c
    exact (IutInitialThetaFiniteFactorRegion.region_subset_normalization D _ _ _).trans
      (IutInitialThetaFinitePacketRegion.packet D p j c).normalization_subset_saturatedLogShell
  | infinite =>
    intro c
    exact (LocalArchimedean.factorOrbit_archLogShell c).subset

theorem closure_sourceFamily_le_shellFamily (j : ℕ) :
    adelicClosure D j (sourceFamily D j) ≤ shellFamily D j := by
  rw [← adelicClosure_shellFamily D j]
  exact (adelicClosure D j).monotone (sourceFamily_le_shellFamily D j)

theorem productRegion_subset_closure (j : ℕ) (U : Family D j) (vQ : RationalPlace) :
    productRegion D j vQ (U vQ) ⊆ productRegion D j vQ (adelicClosure D j U vQ) :=
  productRegion_mono D j vQ ((adelicClosure D j).le_closure U vQ)

theorem family_support_closure_subset (j : ℕ) (U : Family D j) :
    {vQ | adelicClosure D j U vQ ≠ integralFamily D j vQ} ⊆
      {vQ | U vQ ≠ integralFamily D j vQ} := by
  intro vQ hU heq
  apply hU
  change packetClosure D j vQ (U vQ) = integralFamily D j vQ
  rw [heq, packetClosure_integralFamily]

theorem family_finite_support_closure (j : ℕ) (U : Family D j)
    (hU : {vQ | U vQ ≠ integralFamily D j vQ}.Finite) :
    {vQ | adelicClosure D j U vQ ≠ integralFamily D j vQ}.Finite :=
  hU.subset (family_support_closure_subset D j U)

theorem sourceFamily_support_subset (j : ℕ) :
    {vQ | sourceFamily D j vQ ≠ integralFamily D j vQ} ⊆
      (IutInitialThetaAdelicPacketRegion.exceptionalPlaces D : Set RationalPlace) := by
  intro vQ hU
  by_contra hv
  apply hU
  cases vQ with
  | infinite => exact False.elim (hv (Finset.mem_insert_self _ _))
  | finite p =>
    funext c
    apply Subtype.ext
    apply IutInitialThetaFiniteFactorRegion.region_eq_normalization_of_not_bad
    intro hp
    exact hv ((IutInitialThetaAdelicPacketRegion.finite_mem_exceptionalPlaces D p).mpr
      ((IutInitialThetaFinitePacketLogVolume.mem_badPrimes D p).mpr hp))

theorem sourceFamily_finite_support (j : ℕ) :
    {vQ | sourceFamily D j vQ ≠ integralFamily D j vQ}.Finite :=
  (IutInitialThetaAdelicPacketRegion.exceptionalPlaces D).finite_toSet.subset
    (sourceFamily_support_subset D j)

theorem closure_sourceFamily_finite_support (j : ℕ) :
    {vQ | adelicClosure D j (sourceFamily D j) vQ ≠ integralFamily D j vQ}.Finite :=
  family_finite_support_closure D j _ (sourceFamily_finite_support D j)

theorem productRegion_closure_finite_support (j : ℕ) (U : Family D j)
    (hU : {vQ | U vQ ≠ integralFamily D j vQ}.Finite) :
    {vQ | productRegion D j vQ (adelicClosure D j U vQ) ≠ integralRegion D j vQ}.Finite := by
  apply (family_finite_support_closure D j U hU).subset
  intro vQ hv heq
  apply hv
  rw [heq, productRegion_integralFamily]

theorem productRegion_closure_idem (j : ℕ) (U : Family D j) (vQ : RationalPlace) :
    productRegion D j vQ (adelicClosure D j (adelicClosure D j U) vQ) =
      productRegion D j vQ (adelicClosure D j U vQ) := by
  rw [(adelicClosure D j).idempotent]

end
end JoshiTeich.Act1Scene1.IutInitialThetaAdelicHullClosure
