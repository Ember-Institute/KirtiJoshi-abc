import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPaperVossPrimeFiberMultiplicity

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField

universe u
noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

/-!
source-id: JT-SCENE1-PAPER-VOSS-PRIME-FIBER-COVERAGE-20261108
source: Joshi III prime-indexed odd semistable carrier and the actual
VBad section representative fiber map.
fidelity: the existing representative map is injective. This unit records
the resulting exact finite-fiber upper bound and proves that equality is
equivalent to surjectivity onto the concrete section/Voss fiber.
boundary: this is a concrete carrier theorem. It does not identify the
section/Voss carrier with the paper's independent L' representatives, and it
does not prove coverage for arbitrary InitialThetaData.
-/

theorem iutInitialThetaVBadRepresentativePrimeFiber_card_le_sectionVossPrimeFiber_card
    (p : ℕ) :
    Fintype.card (iutInitialThetaVBadRepresentativePrimeFiber D p) ≤
      Fintype.card (iutInitialThetaSectionVossPrimeFiber D p) :=
  Fintype.card_le_of_injective
    (iutInitialThetaVBadRepresentativePrimeFiberMap D p)
    (iutInitialThetaVBadRepresentativePrimeFiberMap_injective D p)

theorem iutInitialThetaVBadRepresentativePrimeFiberMap_surjective_iff_card_eq
    (p : ℕ) :
    Function.Surjective (iutInitialThetaVBadRepresentativePrimeFiberMap D p) ↔
      Fintype.card (iutInitialThetaVBadRepresentativePrimeFiber D p) =
        Fintype.card (iutInitialThetaSectionVossPrimeFiber D p) := by
  constructor
  · intro hsurj
    exact Fintype.card_of_bijective
      ⟨iutInitialThetaVBadRepresentativePrimeFiberMap_injective D p, hsurj⟩
  · intro hcard
    exact ((Fintype.bijective_iff_injective_and_card
      (iutInitialThetaVBadRepresentativePrimeFiberMap D p)).mpr
      ⟨iutInitialThetaVBadRepresentativePrimeFiberMap_injective D p, hcard⟩).2

end
end JoshiTeich.Act1Scene1
