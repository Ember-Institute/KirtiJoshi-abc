import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPaperVossPrimeFiberCoverage
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVossOmittedPrimeFibers

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField

universe u
noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

/-!
source-id: JT-SCENE1-PAPER-VOSS-FIBER-COVERAGE-20261108
source: Joshi III prime-indexed odd semistable carrier and the actual
section/Voss representative image; the existing omitted-fiber coverage theorem.
fidelity: combines the per-residue-characteristic representative maps into a
global concrete-carrier criterion.
boundary: this remains an actual section/Voss criterion. It does not identify
the carrier with paper `L'`, and it does not prove the coverage condition for
arbitrary InitialThetaData.
-/

theorem iutInitialThetaVBadRepresentativePrimeFiberMap_all_surjective_iff_carrier_eq :
    (∀ p : ℕ,
      Function.Surjective (iutInitialThetaVBadRepresentativePrimeFiberMap D p)) ↔
      iutInitialThetaSectionVoss D =
        iutInitialThetaVBadSectionRepresentativeImage D := by
  constructor
  · intro hsurj
    apply Set.Subset.antisymm
    · intro w hw
      let wf : iutInitialThetaSectionVossPrimeFiber D (Arithmetic.residueChar w) :=
        ⟨w, ⟨hw, rfl⟩⟩
      obtain ⟨v, hv⟩ := hsurj (Arithmetic.residueChar w) wf
      exact ⟨v.1, congrArg Subtype.val hv⟩
    · rintro w ⟨v, rfl⟩
      exact iutInitialThetaVBadSectionRepresentative_mem_sectionVoss D v
  · intro hcarrier p
    intro w
    have hwImage : w.1 ∈ iutInitialThetaVBadSectionRepresentativeImage D := by
      rw [← hcarrier]
      exact w.2.1
    obtain ⟨v, hv⟩ := hwImage
    refine ⟨⟨v, ?_⟩, ?_⟩
    · rw [hv]
      exact w.2.2
    · apply Subtype.ext
      exact hv

theorem iutInitialThetaVBadRepresentativePrimeFiberMap_all_surjective_iff_support_coverage :
    (∀ p : ℕ,
      Function.Surjective (iutInitialThetaVBadRepresentativePrimeFiberMap D p)) ↔
      iutInitialThetaVBadModuliFinset D = iutInitialThetaOddModSupportFinset D :=
  (iutInitialThetaVBadRepresentativePrimeFiberMap_all_surjective_iff_carrier_eq D).trans
    (VossOmittedPrimeFibers.sectionVoss_eq_representativeImage_iff_coverage D)

end
end JoshiTeich.Act1Scene1
