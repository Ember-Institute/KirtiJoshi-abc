import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPaperVossPrimeCarrier

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField

universe u

noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

/-!
source-id: JT-SCENE1-PAPER-VOSS-PRIME-FIBER-MULTIPLICITY
source: Joshi III, the prime-indexed odd semistable carrier
underline V odd,ss_p, together with the actual section/Voss
characterization and the injective VBad section representative.
fidelity: defines the finite concrete prime fibers, the corresponding actual
VBad representative fibers, and proves that the representative image fiber
has exactly the cardinality of its source fiber.  This is an actual
multiplicity certificate for the chosen section image.
boundary: this does not identify the concrete carrier with the paper's
independently chosen L' representative system, and it does not prove the
paper fiber multiplicity, omitted mass, or mixed-moduli descent.
-/

/-- The finite concrete section/Voss fiber at rational residue characteristic p. -/
abbrev iutInitialThetaSectionVossPrimeFiber (p : ℕ) :=
  {w : NumberField.FinitePlace ↥D.prime.torsionField //
    w ∈ iutInitialThetaSectionVossAtPrime D p}

/-- Every concrete prime fiber is a finite type. -/
noncomputable instance iutInitialThetaSectionVossPrimeFiberFintype (p : ℕ) :
    Fintype (iutInitialThetaSectionVossPrimeFiber D p) :=
  (iutInitialThetaSectionVossAtPrime_finite D p).fintype

/-- The finite actual VBad source fiber selected by the section representative. -/
abbrev iutInitialThetaVBadRepresentativePrimeFiber (p : ℕ) :=
  {v : iutInitialThetaVBadModuliFinset D //
    Arithmetic.residueChar (iutInitialThetaVBadSectionRepresentative D v) = p}

/-- The source fiber embeds into the concrete section/Voss fiber. -/
def iutInitialThetaVBadRepresentativePrimeFiberMap (p : ℕ) :
    iutInitialThetaVBadRepresentativePrimeFiber D p →
      iutInitialThetaSectionVossPrimeFiber D p :=
  fun v =>
    ⟨iutInitialThetaVBadSectionRepresentative D v.1,
      ⟨(iutInitialThetaVBadSectionRepresentative_mem_sectionVoss D v.1),
        v.2⟩⟩

theorem iutInitialThetaVBadRepresentativePrimeFiberMap_injective (p : ℕ) :
    Function.Injective (iutInitialThetaVBadRepresentativePrimeFiberMap D p) := by
  intro v₁ v₂ h
  apply Subtype.ext
  apply iutInitialThetaVBadSectionRepresentative_injective D
  exact congrArg Subtype.val h

/-- The range of the actual representative map inside one concrete prime fiber. -/
def iutInitialThetaVBadRepresentativePrimeFiberImage (p : ℕ) :
    Set (iutInitialThetaSectionVossPrimeFiber D p) :=
  Set.range (iutInitialThetaVBadRepresentativePrimeFiberMap D p)

/-- The concrete section fiber of the actual representative image. -/
def iutInitialThetaVBadRepresentativePrimeFiberImageType (p : ℕ) :=
  {w : iutInitialThetaSectionVossPrimeFiber D p //
    w ∈ iutInitialThetaVBadRepresentativePrimeFiberImage D p}

/-- The source fiber is equivalent to its concrete representative image fiber. -/
noncomputable def iutInitialThetaVBadRepresentativePrimeFiberEquiv (p : ℕ) :
    iutInitialThetaVBadRepresentativePrimeFiber D p ≃
      iutInitialThetaVBadRepresentativePrimeFiberImageType D p := by
  classical
  refine Equiv.ofBijective
    (fun v =>
      ⟨iutInitialThetaVBadRepresentativePrimeFiberMap D p v, ⟨v, rfl⟩⟩) ?_
  constructor
  · intro v₁ v₂ h
    exact iutInitialThetaVBadRepresentativePrimeFiberMap_injective D p
      (congrArg Subtype.val h)
  · intro w
    rcases w.2 with ⟨v, hv⟩
    exact ⟨v, Subtype.ext hv⟩

noncomputable instance iutInitialThetaVBadRepresentativePrimeFiberImageTypeFintype
    (p : ℕ) :
    Fintype (iutInitialThetaVBadRepresentativePrimeFiberImageType D p) :=
  (Set.finite_range (iutInitialThetaVBadRepresentativePrimeFiberMap D p)).fintype

theorem iutInitialThetaVBadRepresentativePrimeFiberImageType_card (p : ℕ) :
    Fintype.card (iutInitialThetaVBadRepresentativePrimeFiberImageType D p) =
      Fintype.card (iutInitialThetaVBadRepresentativePrimeFiber D p) := by
  simpa using Fintype.card_congr
    (iutInitialThetaVBadRepresentativePrimeFiberEquiv D p).symm

/-- Concrete prime-fiber multiplicity of the full section/Voss carrier. -/
def iutInitialThetaSectionVossPrimeMultiplicity (p : ℕ) : ℕ :=
  Fintype.card (iutInitialThetaSectionVossPrimeFiber D p)

/-- Actual VBad representative multiplicity in the same concrete fiber. -/
def iutInitialThetaVBadRepresentativePrimeMultiplicity (p : ℕ) : ℕ :=
  Fintype.card (iutInitialThetaVBadRepresentativePrimeFiber D p)

/-- The actual representative image has the source-fiber multiplicity exactly. -/
theorem iutInitialThetaVBadRepresentativePrimeFiberImage_card (p : ℕ) :
    Fintype.card (iutInitialThetaVBadRepresentativePrimeFiberImageType D p) =
      iutInitialThetaVBadRepresentativePrimeMultiplicity D p := by
  exact iutInitialThetaVBadRepresentativePrimeFiberImageType_card D p

end
end JoshiTeich.Act1Scene1
