import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPaperVossPrimeFiberMultiplicity
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadSelectedSupportDefect

/-!
source-id: JT-SCENE1-INITIAL-THETA-VOSS-OMITTED-PRIME-FIBERS
source: Joshi III `ss:theta-data-fixing2`, `ss:val-sets-defn` (1028--1055),
the actual section/Voss prime fibers, and the proved VBad selected-paper
support defect.
fidelity: constructs the omitted part of each full concrete section fiber,
proves exact selected-plus-omitted multiplicity accounting, and identifies
vanishing of all omitted multiplicities with full moduli-support coverage
and with vanishing of the existing omitted positive paper-log sum.
boundary: Scene1/Derived; no coverage law is assumed or proved for arbitrary
initial data. Paper L' identity, paper multiplicity and mixed-moduli descent
remain open. Original proofs; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1.VossOmittedPrimeFibers

open JoshiTeich.Prologue
open scoped Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

abbrev OmittedPrimeFiber (p : ℕ) :=
  {w : iutInitialThetaSectionVossPrimeFiber D p //
    w ∉ iutInitialThetaVBadRepresentativePrimeFiberImage D p}

noncomputable instance omittedPrimeFiberFintype (p : ℕ) :
    Fintype (OmittedPrimeFiber D p) := Fintype.ofFinite _

def omittedPrimeMultiplicity (p : ℕ) : ℕ := Fintype.card (OmittedPrimeFiber D p)

theorem primeMultiplicity_eq_selected_add_omitted (p : ℕ) :
    iutInitialThetaSectionVossPrimeMultiplicity D p =
      iutInitialThetaVBadRepresentativePrimeMultiplicity D p +
        omittedPrimeMultiplicity D p := by
  change Fintype.card (iutInitialThetaSectionVossPrimeFiber D p) =
    iutInitialThetaVBadRepresentativePrimeMultiplicity D p +
      Fintype.card (OmittedPrimeFiber D p)
  rw [← iutInitialThetaVBadRepresentativePrimeFiberImage_card D p]
  have hcompl := @Fintype.card_subtype_compl
    (iutInitialThetaSectionVossPrimeFiber D p) inferInstance
    (fun w : iutInitialThetaSectionVossPrimeFiber D p =>
      w ∈ iutInitialThetaVBadRepresentativePrimeFiberImage D p)
    (iutInitialThetaVBadRepresentativePrimeFiberImageTypeFintype D p)
    (omittedPrimeFiberFintype D p)
  change Fintype.card (OmittedPrimeFiber D p) =
    Fintype.card (iutInitialThetaSectionVossPrimeFiber D p) -
      Fintype.card (iutInitialThetaVBadRepresentativePrimeFiberImageType D p) at hcompl
  rw [hcompl]
  exact (Nat.add_sub_of_le (Fintype.card_le_of_injective
    (fun w : iutInitialThetaVBadRepresentativePrimeFiberImageType D p => w.1)
    Subtype.val_injective)).symm

theorem omittedPrimeMultiplicity_eq_zero_iff (p : ℕ) :
    omittedPrimeMultiplicity D p = 0 ↔
      ∀ w : iutInitialThetaSectionVossPrimeFiber D p,
        w ∈ iutInitialThetaVBadRepresentativePrimeFiberImage D p := by
  change Fintype.card (OmittedPrimeFiber D p) = 0 ↔ _
  rw [Fintype.card_eq_zero_iff]
  constructor
  · intro h w
    by_contra hw
    exact h.false ⟨w, hw⟩
  · intro h
    exact ⟨fun w => w.2 (h w.1)⟩

theorem primeMultiplicity_lt_iff_omitted_pos (p : ℕ) :
    iutInitialThetaVBadRepresentativePrimeMultiplicity D p <
        iutInitialThetaSectionVossPrimeMultiplicity D p ↔
      0 < omittedPrimeMultiplicity D p := by
  rw [primeMultiplicity_eq_selected_add_omitted D p]
  omega

theorem sectionVoss_eq_representativeImage_iff_coverage :
    iutInitialThetaSectionVoss D = iutInitialThetaVBadSectionRepresentativeImage D ↔
      iutInitialThetaVBadModuliFinset D = iutInitialThetaOddModSupportFinset D := by
  constructor
  · intro heq
    apply Finset.Subset.antisymm (Finset.filter_subset _ _)
    intro v hv
    have hw : iutInitialThetaFinitePlaceSection D v ∈ iutInitialThetaSectionVoss D := by
      rw [← iutInitialThetaOddTateSectionPlaces_eq_sectionVoss D,
        iutInitialThetaOddTateSectionPlaces_eq_selectedSupport D]
      exact ⟨v, (iutInitialThetaOddModSupport_finite D).mem_toFinset.mp hv, rfl⟩
    rw [heq] at hw
    obtain ⟨w, hw⟩ := hw
    have hvw : w.1 = v := iutInitialThetaFinitePlaceSection_injective D hw
    exact hvw ▸ w.2
  · intro hcover
    apply Set.Subset.antisymm
    · intro w hw
      rw [← iutInitialThetaOddTateSectionPlaces_eq_sectionVoss D,
        iutInitialThetaOddTateSectionPlaces_eq_selectedSupport D] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      have hvbad : v ∈ iutInitialThetaVBadModuliFinset D := by
        rw [hcover]
        exact (iutInitialThetaOddModSupport_finite D).mem_toFinset.mpr hv
      exact ⟨⟨v, hvbad⟩, rfl⟩
    · rintro w ⟨v, rfl⟩
      exact iutInitialThetaVBadSectionRepresentative_mem_sectionVoss D v

theorem all_omitted_eq_zero_iff_carrier :
    (∀ p, omittedPrimeMultiplicity D p = 0) ↔
      iutInitialThetaSectionVoss D = iutInitialThetaVBadSectionRepresentativeImage D := by
  constructor
  · intro hz
    apply Set.Subset.antisymm
    · intro w hw
      let wf : iutInitialThetaSectionVossPrimeFiber D (Arithmetic.residueChar w) :=
        ⟨w, ⟨hw, rfl⟩⟩
      have himage := (omittedPrimeMultiplicity_eq_zero_iff D _).mp (hz _) wf
      obtain ⟨v, hv⟩ := himage
      exact ⟨v.1, congrArg Subtype.val hv⟩
    · rintro w ⟨v, rfl⟩
      exact iutInitialThetaVBadSectionRepresentative_mem_sectionVoss D v
  · intro heq p
    apply (omittedPrimeMultiplicity_eq_zero_iff D p).mpr
    intro w
    have himage : w.1 ∈ iutInitialThetaVBadSectionRepresentativeImage D := by
      rw [← heq]
      exact w.2.1
    obtain ⟨v, hv⟩ := himage
    refine ⟨⟨v, ?_⟩, ?_⟩
    · rw [hv]
      exact w.2.2
    · apply Subtype.ext
      exact hv

theorem all_omitted_eq_zero_iff_coverage :
    (∀ p, omittedPrimeMultiplicity D p = 0) ↔
      iutInitialThetaVBadModuliFinset D = iutInitialThetaOddModSupportFinset D :=
  (all_omitted_eq_zero_iff_carrier D).trans
    (sectionVoss_eq_representativeImage_iff_coverage D)

theorem omittedPaperSum_eq_zero_iff_all_omitted_eq_zero :
    VBadSelectedPaper.omittedPaperSum D = 0 ↔
      ∀ p, omittedPrimeMultiplicity D p = 0 :=
  (VBadSelectedPaper.omittedPaperSum_eq_zero_iff_coverage D).trans
    (all_omitted_eq_zero_iff_coverage D).symm

theorem exists_primeMultiplicity_gap_of_missing
    (hmissing : iutInitialThetaVBadModuliFinset D ≠ iutInitialThetaOddModSupportFinset D) :
    ∃ p ∈ iutInitialThetaSectionVossPrimeSupport D,
      iutInitialThetaVBadRepresentativePrimeMultiplicity D p <
        iutInitialThetaSectionVossPrimeMultiplicity D p := by
  have hnot : ¬ ∀ p, omittedPrimeMultiplicity D p = 0 :=
    fun h => hmissing ((all_omitted_eq_zero_iff_coverage D).mp h)
  obtain ⟨p, hp⟩ := not_forall.mp hnot
  have hlt := (primeMultiplicity_lt_iff_omitted_pos D p).mpr (Nat.pos_of_ne_zero hp)
  have hpos : 0 < Fintype.card (iutInitialThetaSectionVossPrimeFiber D p) :=
    lt_of_le_of_lt (Nat.zero_le _) hlt
  obtain ⟨w⟩ := Fintype.card_pos_iff.mp hpos
  exact ⟨p, ⟨w.1, w.2.1, w.2.2⟩, hlt⟩

theorem omittedPaperSum_pos_iff_exists_primeMultiplicity_gap :
    0 < VBadSelectedPaper.omittedPaperSum D ↔
      ∃ p ∈ iutInitialThetaSectionVossPrimeSupport D,
        iutInitialThetaVBadRepresentativePrimeMultiplicity D p <
          iutInitialThetaSectionVossPrimeMultiplicity D p := by
  constructor
  · intro hpos
    apply exists_primeMultiplicity_gap_of_missing D
    intro hcover
    exact (ne_of_gt hpos)
      ((VBadSelectedPaper.omittedPaperSum_eq_zero_iff_coverage D).mpr hcover)
  · rintro ⟨p, _, hgap⟩
    apply lt_of_le_of_ne (VBadSelectedPaper.omittedPaperSum_nonneg D)
    intro hz
    have hzero := (omittedPaperSum_eq_zero_iff_all_omitted_eq_zero D).mp hz.symm
    have hpos := (primeMultiplicity_lt_iff_omitted_pos D p).mp hgap
    rw [hzero p] at hpos
    exact (lt_irrefl 0) hpos

end
end JoshiTeich.Act1Scene1.VossOmittedPrimeFibers
