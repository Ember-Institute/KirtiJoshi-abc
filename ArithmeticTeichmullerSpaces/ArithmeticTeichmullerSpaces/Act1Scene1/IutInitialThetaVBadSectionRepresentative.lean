import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadModuliJAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadSelectedPaperAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVoss

/-!
source-id: JT-SCENE1-INITIAL-THETA-VBAD-SECTION-REPRESENTATIVE
source: the actual `InitialThetaData` finite-place section and the actual
`VBad` moduli carrier.
fidelity: maps every actual `VBad` moduli place to its selected torsion-field
section place, proves injectivity and membership in the actual section/Voss
carrier. This is an actual representative map, not an identification with
the paper's independently chosen `L'` representatives.
boundary: Scene1/Derived; paper representative multiplicity and paper carrier
identity remain explicit obligations.
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue NumberField

universe u

noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

def iutInitialThetaVBadSectionRepresentative
    (v : iutInitialThetaVBadModuliFinset D) :
    NumberField.FinitePlace ↥D.prime.torsionField :=
  iutInitialThetaFinitePlaceSection D v.1

theorem iutInitialThetaVBadSectionRepresentative_injective :
    Function.Injective (iutInitialThetaVBadSectionRepresentative D) := by
  intro v₁ v₂ h
  apply Subtype.ext
  exact iutInitialThetaFinitePlaceSection_injective D h

theorem iutInitialThetaVBadSectionRepresentative_mem_sectionVoss
    (v : iutInitialThetaVBadModuliFinset D) :
    iutInitialThetaVBadSectionRepresentative D v ∈
      iutInitialThetaSectionVoss D := by
  have hv : v.1 ∈ D.VBad :=
    (mem_iutInitialThetaVBadModuliFinset_iff D v.1).mp v.2
  have hvPort : v.1 ∈ iutVBadOddModSupportPort D :=
    iutInitialThetaVBad_subset_VBadOdd D hv
  have hodd : Odd (Arithmetic.residueChar v.1) := by
    have hp := Arithmetic.residueChar_prime v.1
    rcases hp.eq_two_or_odd' with htwo | hodd
    · exact (hvPort.1 htwo).elim
    · exact hodd
  rw [← iutInitialThetaOddTateSectionPlaces_eq_sectionVoss D]
  exact ⟨v.1, rfl, hodd,
    ⟨iutInitialThetaFinitePlaceSection_tateStructure D v.1 hvPort⟩⟩

def iutInitialThetaVBadSectionRepresentativeImage :
    Set (NumberField.FinitePlace ↥D.prime.torsionField) :=
  Set.range (iutInitialThetaVBadSectionRepresentative D)

theorem iutInitialThetaVBadSectionRepresentativeImage_finite :
    (iutInitialThetaVBadSectionRepresentativeImage D).Finite := by
  exact Set.finite_range _

noncomputable def iutInitialThetaVBadSectionRepresentativeEquiv :
    iutInitialThetaVBadModuliFinset D ≃
      {w : NumberField.FinitePlace ↥D.prime.torsionField //
        w ∈ iutInitialThetaVBadSectionRepresentativeImage D} := by
  classical
  refine Equiv.ofBijective
    (fun v => ⟨iutInitialThetaVBadSectionRepresentative D v, ⟨v, rfl⟩⟩) ?_
  constructor
  · intro v₁ v₂ h
    apply Subtype.ext
    exact iutInitialThetaVBadSectionRepresentative_injective D
      (congrArg (fun w : {w : NumberField.FinitePlace ↥D.prime.torsionField //
        w ∈ iutInitialThetaVBadSectionRepresentativeImage D} => w.1) h)
  · intro w
    rcases w.2 with ⟨v, hv⟩
    exact ⟨v, Subtype.ext hv.symm⟩

theorem iutInitialThetaVBadSectionRepresentativeImage_card :
    Fintype.card
        {w : NumberField.FinitePlace ↥D.prime.torsionField //
          w ∈ iutInitialThetaVBadSectionRepresentativeImage D} =
      Fintype.card (iutInitialThetaVBadModuliFinset D) := by
  simpa using Fintype.card_congr (iutInitialThetaVBadSectionRepresentativeEquiv D).symm

theorem iutInitialThetaVBadSectionRepresentative_sum_transport
    (f : iutInitialThetaVBadModuliFinset D → ℝ) :
    (∑ v : iutInitialThetaVBadModuliFinset D, f v) =
      ∑ w : {w : NumberField.FinitePlace ↥D.prime.torsionField //
        w ∈ iutInitialThetaVBadSectionRepresentativeImage D},
        f ((iutInitialThetaVBadSectionRepresentativeEquiv D).symm w) := by
  simpa using
    (iutInitialThetaVBadSectionRepresentativeEquiv D).sum_comp
      (fun w => f ((iutInitialThetaVBadSectionRepresentativeEquiv D).symm w))

theorem iutInitialThetaVBadSectionRepresentative_eq_selectedSourceAt
    (v : iutInitialThetaVBadModuliFinset D) :
    iutInitialThetaVBadSectionRepresentative D v =
      (VBadSelectedPaper.sourceAt D v).1 := by
  rfl

theorem iutInitialThetaVBadSectionRepresentative_paperTerm_sum_transport :
    (∑ v : iutInitialThetaVBadModuliFinset D,
      VBadSelectedPaper.paperTerm D v) =
      ∑ w : {w : NumberField.FinitePlace ↥D.prime.torsionField //
        w ∈ iutInitialThetaVBadSectionRepresentativeImage D},
        VBadSelectedPaper.paperTerm D
          ((iutInitialThetaVBadSectionRepresentativeEquiv D).symm w) := by
  exact iutInitialThetaVBadSectionRepresentative_sum_transport D
    (fun v => VBadSelectedPaper.paperTerm D v)

theorem iutInitialThetaVBadSectionRepresentative_weightedPaperTerm_sum_transport :
    (∑ v : iutInitialThetaVBadModuliFinset D,
      iutInitialThetaRepresentativeCoefficient D
          (iutInitialThetaVBadModuliAt D v) * VBadSelectedPaper.paperTerm D v) =
      ∑ w : {w : NumberField.FinitePlace ↥D.prime.torsionField //
        w ∈ iutInitialThetaVBadSectionRepresentativeImage D},
        iutInitialThetaRepresentativeCoefficient D
            (iutInitialThetaVBadModuliAt D
              ((iutInitialThetaVBadSectionRepresentativeEquiv D).symm w)) *
          VBadSelectedPaper.paperTerm D
            ((iutInitialThetaVBadSectionRepresentativeEquiv D).symm w) := by
  exact iutInitialThetaVBadSectionRepresentative_sum_transport D
    (fun v => iutInitialThetaRepresentativeCoefficient D
      (iutInitialThetaVBadModuliAt D v) * VBadSelectedPaper.paperTerm D v)

theorem iutInitialThetaVBadSectionRepresentative_referenceAbsLogQ_eq_image_sum :
    JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) =
      ∑ w : {w : NumberField.FinitePlace ↥D.prime.torsionField //
        w ∈ iutInitialThetaVBadSectionRepresentativeImage D},
        iutInitialThetaRepresentativeCoefficient D
            (iutInitialThetaVBadModuliAt D
              ((iutInitialThetaVBadSectionRepresentativeEquiv D).symm w)) *
          VBadSelectedPaper.paperTerm D
            ((iutInitialThetaVBadSectionRepresentativeEquiv D).symm w) := by
  rw [VBadSelectedPaper.referenceAbsLogQ_eq_coefficientWeightedPaperSum D]
  exact iutInitialThetaVBadSectionRepresentative_weightedPaperTerm_sum_transport D

theorem iutInitialThetaVBadSectionRepresentative_referenceAbsLogQ_lt_image_unweighted_sum :
    JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) <
      ∑ w : {w : NumberField.FinitePlace ↥D.prime.torsionField //
        w ∈ iutInitialThetaVBadSectionRepresentativeImage D},
        VBadSelectedPaper.paperTerm D
          ((iutInitialThetaVBadSectionRepresentativeEquiv D).symm w) := by
  have h := VBadSelectedPaper.referenceAbsLogQ_lt_paperSum D
  simpa [VBadSelectedPaper.paperSum,
    iutInitialThetaVBadSectionRepresentative_paperTerm_sum_transport D] using h

def iutInitialThetaVBadSectionRepresentativeRootProduct : ℝ :=
  ∏ w : {w : NumberField.FinitePlace ↥D.prime.torsionField //
    w ∈ iutInitialThetaVBadSectionRepresentativeImage D},
    actualPaperRootNorm D
      (VBadSelectedPaper.sourceAt D
        ((iutInitialThetaVBadSectionRepresentativeEquiv D).symm w))

theorem iutInitialThetaVBadSectionRepresentativeRootProduct_pos :
    0 < iutInitialThetaVBadSectionRepresentativeRootProduct D := by
  unfold iutInitialThetaVBadSectionRepresentativeRootProduct
  exact Finset.prod_pos fun w _ =>
    (actualPaperRootNorm_mem_Ioo D _).1

theorem iutInitialThetaVBadSectionRepresentative_negLogRootProduct_eq_image_sum :
    -Real.log (iutInitialThetaVBadSectionRepresentativeRootProduct D) =
      ∑ w : {w : NumberField.FinitePlace ↥D.prime.torsionField //
        w ∈ iutInitialThetaVBadSectionRepresentativeImage D},
        VBadSelectedPaper.paperTerm D
          ((iutInitialThetaVBadSectionRepresentativeEquiv D).symm w) := by
  rw [iutInitialThetaVBadSectionRepresentativeRootProduct,
    Real.log_prod (fun w _ => (actualPaperRootNorm_mem_Ioo D _).1.ne'),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  unfold VBadSelectedPaper.paperTerm
  rfl

theorem iutInitialThetaVBadSectionRepresentativeRootProduct_lt_normalizedVBadRootProduct :
    iutInitialThetaVBadSectionRepresentativeRootProduct D <
      iutInitialThetaNormalizedVBadRelativeQRootProduct D := by
  have h := iutInitialThetaVBadSectionRepresentative_referenceAbsLogQ_lt_image_unweighted_sum D
  rw [← iutInitialThetaNormalizedVBadRelativeQRootProduct_negLog_eq_referenceAbsLogQ D,
    ← iutInitialThetaVBadSectionRepresentative_negLogRootProduct_eq_image_sum D] at h
  exact (Real.log_lt_log_iff
    (iutInitialThetaVBadSectionRepresentativeRootProduct_pos D)
    (iutInitialThetaNormalizedVBadRelativeQRootProduct_pos D)).mp
      (neg_lt_neg_iff.mp h)

end
end JoshiTeich.Act1Scene1
