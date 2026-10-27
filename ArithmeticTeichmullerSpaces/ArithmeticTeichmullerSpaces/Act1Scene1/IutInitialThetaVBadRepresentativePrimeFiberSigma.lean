import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPaperVossPrimeFiberAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPaperVossPrimeFiberMultiplicity

/-!
source-id: JT-SCENE1-INITIAL-THETA-VBAD-REPRESENTATIVE-PRIME-FIBER-SIGMA
source: the actual VBad section representative image, its prime fibers, and
the finite odd semistable carrier; Joshi III 1028--1055.
fidelity: decomposes the concrete VBad representative image by rational
residue characteristic and transports its cardinality to a finite Sigma of
actual prime fibers. This is an actual finite-carrier identity and does not
identify the image with paper `L'` representatives.
boundary: Scene1/Derived; omitted mass and mixed-moduli descent remain open.
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField
open scoped Classical

universe u
noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

abbrev RepresentativeImage :=
  {w : NumberField.FinitePlace ↥D.prime.torsionField //
    w ∈ iutInitialThetaVBadSectionRepresentativeImage D}

noncomputable instance representativeImageFintype :
    Fintype (RepresentativeImage D) :=
  (iutInitialThetaVBadSectionRepresentativeImage_finite D).fintype

def RepresentativePrimeSupport : Set ℕ :=
  (fun w : RepresentativeImage D => Arithmetic.residueChar w.1) '' Set.univ

abbrev RepresentativePrimeSupportType :=
  {p : ℕ // p ∈ RepresentativePrimeSupport D}

noncomputable instance representativePrimeSupportFintype :
    Fintype (RepresentativePrimeSupportType D) := by
  apply Set.Finite.fintype
  change ((fun w : RepresentativeImage D => Arithmetic.residueChar w.1) ''
    (Set.univ : Set (RepresentativeImage D))).Finite
  exact Set.finite_univ.image _

abbrev RepresentativePrimeFiber (p : ℕ) :=
  {w : RepresentativeImage D // Arithmetic.residueChar w.1 = p}

noncomputable instance representativePrimeFiberFintype (p : ℕ) :
    Fintype (RepresentativePrimeFiber D p) := by
  exact Fintype.ofFinite _

theorem representativePrimeSupport_mem_iff (p : ℕ) :
    p ∈ RepresentativePrimeSupport D ↔
      ∃ w : RepresentativeImage D, Arithmetic.residueChar w.1 = p := by
  constructor
  · rintro ⟨w, -, rfl⟩
    exact ⟨w, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w, Set.mem_univ _, rfl⟩

noncomputable def representativeImagePrimeFiberSigmaEquiv :
    RepresentativeImage D ≃
      Σ p : RepresentativePrimeSupportType D, RepresentativePrimeFiber D p.1 := by
  classical
  refine Equiv.ofBijective
    (fun w => ⟨⟨Arithmetic.residueChar w.1, ⟨w, Set.mem_univ _, rfl⟩⟩,
      ⟨w, rfl⟩⟩) ?_
  constructor
  · intro w₁ w₂ h
    apply Subtype.ext
    change w₁.1 = w₂.1
    exact congrArg (fun z => z.2.1.1) h
  · rintro ⟨⟨p, hp⟩, w⟩
    rcases w with ⟨w, hw⟩
    cases hw
    exact ⟨w, rfl⟩

theorem representativeImage_card_eq_primeFiber_sum :
    Fintype.card (RepresentativeImage D) =
      ∑ p : RepresentativePrimeSupportType D,
        Fintype.card (RepresentativePrimeFiber D p.1) := by
  rw [Fintype.card_congr (representativeImagePrimeFiberSigmaEquiv D),
    Fintype.card_sigma]

theorem representativeImage_card_eq_vbad_card :
    Fintype.card (RepresentativeImage D) =
      Fintype.card (iutInitialThetaVBadModuliFinset D) :=
  iutInitialThetaVBadSectionRepresentativeImage_card D

end
end JoshiTeich.Act1Scene1
