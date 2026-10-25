import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadSectionRepresentative

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField

universe u

noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

/-!
source-id: JT-SCENE1-PAPER-VOSS-PRIME-CARRIER
source: Joshi III, `Arithmetic Teichmuller Spaces 3.tex`, definitions around
`\\underline{\\mathbb V}^{odd,ss}` and `\\underline{\\mathbb V}^{odd,ss}_p`
(1042--1055); reference `ValuationSection.Vbad` and the actual section/Voss
characterization in `IutInitialThetaVoss.lean`.
fidelity: partitions the concrete section/Voss carrier by the rational residue
characteristic.  It proves finiteness, odd-prime support, disjoint fibers, and
the exact finite union over the prime support.  It also places each actual
VBad section representative in its corresponding fiber.
boundary: this is a concrete carrier decomposition.  It does not identify
the carrier with an independently chosen L' representative system, does not
prove fiber multiplicities, and does not construct a holomorphoid or paper
theta-volume source.
-/

/-- The paper's `\\underline{\\mathbb V}^{odd,ss}_p` fiber for the concrete section. -/
def iutInitialThetaSectionVossAtPrime (p : ℕ) :
    Set (NumberField.FinitePlace ↥D.prime.torsionField) :=
  {w | w ∈ iutInitialThetaSectionVoss D ∧ Arithmetic.residueChar w = p}

theorem iutInitialThetaSectionVossAtPrime_subset (p : ℕ) :
    iutInitialThetaSectionVossAtPrime D p ⊆ iutInitialThetaSectionVoss D := by
  intro w hw
  exact hw.1

theorem iutInitialThetaSectionVossAtPrime_finite (p : ℕ) :
    (iutInitialThetaSectionVossAtPrime D p).Finite := by
  exact (iutInitialThetaSectionVoss_finite D).subset
    (iutInitialThetaSectionVossAtPrime_subset D p)

theorem iutInitialThetaSectionVossAtPrime_residueChar_eq
    (p : ℕ) {w : NumberField.FinitePlace ↥D.prime.torsionField}
    (hw : w ∈ iutInitialThetaSectionVossAtPrime D p) :
    Arithmetic.residueChar w = p := by
  exact hw.2

theorem iutInitialThetaSectionVossAtPrime_odd
    (p : ℕ) {w : NumberField.FinitePlace ↥D.prime.torsionField}
    (hw : w ∈ iutInitialThetaSectionVossAtPrime D p) :
    Odd p := by
  have hwOdd : Odd (Arithmetic.residueChar w) := by
    exact (show w ∈ iutInitialThetaOddSemistablePlaces D from hw.1.2).1
  simpa [hw.2] using hwOdd

theorem iutInitialThetaSectionVossAtPrime_prime
    (p : ℕ) {w : NumberField.FinitePlace ↥D.prime.torsionField}
    (hw : w ∈ iutInitialThetaSectionVossAtPrime D p) :
    p.Prime := by
  rw [← hw.2]
  exact Arithmetic.residueChar_prime w

/-- The finite set of rational residue characteristics occurring in the section/Voss carrier. -/
def iutInitialThetaSectionVossPrimeSupport : Set ℕ :=
  (fun w : NumberField.FinitePlace ↥D.prime.torsionField =>
    Arithmetic.residueChar w) '' iutInitialThetaSectionVoss D

theorem iutInitialThetaSectionVossPrimeSupport_finite :
    (iutInitialThetaSectionVossPrimeSupport D).Finite := by
  exact (iutInitialThetaSectionVoss_finite D).image _

theorem mem_iutInitialThetaSectionVossPrimeSupport_iff (p : ℕ) :
    p ∈ iutInitialThetaSectionVossPrimeSupport D ↔
      ∃ w, w ∈ iutInitialThetaSectionVoss D ∧ Arithmetic.residueChar w = p := by
  rfl

theorem iutInitialThetaSectionVossAtPrime_nonempty_iff (p : ℕ) :
    (iutInitialThetaSectionVossAtPrime D p).Nonempty ↔
      p ∈ iutInitialThetaSectionVossPrimeSupport D := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, hw.1, hw.2⟩
  · intro hp
    obtain ⟨w, hw, hwp⟩ := (mem_iutInitialThetaSectionVossPrimeSupport_iff D p).mp hp
    exact ⟨w, ⟨hw, hwp⟩⟩

theorem iutInitialThetaSectionVossAtPrime_disjoint
    {p q : ℕ} (hpq : p ≠ q) :
    Disjoint (iutInitialThetaSectionVossAtPrime D p)
      (iutInitialThetaSectionVossAtPrime D q) := by
  rw [Set.disjoint_left]
  intro w hwp hwq
  have hwp' : Arithmetic.residueChar w = p := hwp.2
  have hwq' : Arithmetic.residueChar w = q := hwq.2
  apply hpq
  calc
    p = Arithmetic.residueChar w := hwp'.symm
    _ = q := hwq'

theorem mem_iutInitialThetaSectionVossAtPrime_of_mem
    {w : NumberField.FinitePlace ↥D.prime.torsionField}
    (hw : w ∈ iutInitialThetaSectionVoss D) :
    w ∈ iutInitialThetaSectionVossAtPrime D (Arithmetic.residueChar w) := by
  exact ⟨hw, rfl⟩

theorem iutInitialThetaSectionVoss_eq_iUnion_primeSupport :
    iutInitialThetaSectionVoss D =
      ⋃ p ∈ iutInitialThetaSectionVossPrimeSupport D,
        iutInitialThetaSectionVossAtPrime D p := by
  ext w
  constructor
  · intro hw
    have hp : Arithmetic.residueChar w ∈ iutInitialThetaSectionVossPrimeSupport D :=
      ⟨w, hw, rfl⟩
    refine Set.mem_iUnion.2 ⟨Arithmetic.residueChar w, ?_⟩
    refine Set.mem_iUnion.2 ⟨hp, ?_⟩
    exact mem_iutInitialThetaSectionVossAtPrime_of_mem D hw
  · intro hw
    obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hw
    obtain ⟨hps, hwp⟩ := Set.mem_iUnion.1 hp
    exact (iutInitialThetaSectionVossAtPrime_subset D p) hwp

theorem iutInitialThetaVBadSectionRepresentative_mem_atPrime
    (v : iutInitialThetaVBadModuliFinset D) :
    iutInitialThetaVBadSectionRepresentative D v ∈
      iutInitialThetaSectionVossAtPrime D
        (Arithmetic.residueChar (iutInitialThetaVBadSectionRepresentative D v)) := by
  exact mem_iutInitialThetaSectionVossAtPrime_of_mem D
    (iutInitialThetaVBadSectionRepresentative_mem_sectionVoss D v)

end
end JoshiTeich.Act1Scene1
