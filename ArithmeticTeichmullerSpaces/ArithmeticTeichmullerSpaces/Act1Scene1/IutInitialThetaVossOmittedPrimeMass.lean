import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVossOmittedPrimeFibers
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPaperVossPrimeFiberAccounting

/-!
source-id: JT-SCENE1-INITIAL-THETA-VOSS-OMITTED-PRIME-MASS
source: Joshi III `ss:val-sets-defn` (1042--1055), `ss:weighted-vol`
(3522--3562), and the actual selected-paper root normalization and support
defect already proved in Scene1.
fidelity: uses the original q-root source at every concrete Voss place.
Partitions the omitted source by rational residue characteristic without
changing its local log term, and proves that the original omitted paper
sum is exactly the sum of the concrete omitted prime-fiber masses.
boundary: Scene1/Derived; no omitted mass is assumed to vanish. Paper L'
representative identity, paper weights and mixed-moduli descent remain open.
Original proofs; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1.VossOmittedPrimeMass

open JoshiTeich.Prologue VossOmittedPrimeFibers
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

abbrev VossPlace :=
  {w : NumberField.FinitePlace ↥D.prime.torsionField // w ∈ iutInitialThetaSectionVoss D}

private theorem voss_mem_selectedPlaces (w : VossPlace D) :
    w.1 ∈ iutInitialThetaOddSupportSelectedQRootPlaces D := by
  rw [iutInitialThetaOddSupportSelectedQRootPlaces_eq_oddTateSectionPlaces D,
    iutInitialThetaOddTateSectionPlaces_eq_sectionVoss D]
  exact w.2

def sourceAt (w : VossPlace D) :
    (iutInitialThetaOddSupportTorsionQRootSource D).badFinset :=
  ⟨w.1, by
    obtain ⟨v, hv, hplace⟩ := voss_mem_selectedPlaces D w
    exact hplace ▸ (iutInitialThetaOddSupportSelectedQRootPlace D v hv).2⟩

theorem sourceAt_mem_fullSelected (w : VossPlace D) :
    sourceAt D w ∈ VBadSelectedPaper.fullSelectedFinset D :=
  (VBadSelectedPaper.mem_fullSelectedFinset_iff D _).mpr
    (voss_mem_selectedPlaces D w)

private theorem sourceAt_mem_selected_iff_image (w : VossPlace D) :
    sourceAt D w ∈ VBadSelectedPaper.selectedFinset D ↔
      w.1 ∈ iutInitialThetaVBadSectionRepresentativeImage D := by
  rw [VBadSelectedPaper.mem_selectedFinset_iff D]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, (iutInitialThetaVBadSectionRepresentative_eq_selectedSourceAt D v).trans
      (congrArg Subtype.val hv)⟩
  · rintro ⟨v, hv⟩
    refine ⟨v, Subtype.ext ?_⟩
    exact (iutInitialThetaVBadSectionRepresentative_eq_selectedSourceAt D v).symm.trans hv

private theorem fiber_mem_image_iff (p : ℕ)
    (w : iutInitialThetaSectionVossPrimeFiber D p) :
    w ∈ iutInitialThetaVBadRepresentativePrimeFiberImage D p ↔
      w.1 ∈ iutInitialThetaVBadSectionRepresentativeImage D := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v.1, congrArg Subtype.val hv⟩
  · rintro ⟨v, hv⟩
    refine ⟨⟨v, ?_⟩, Subtype.ext hv⟩
    rw [hv]
    exact w.2.2

private theorem sourceAt_mem_selected_iff_primeImage (p : ℕ)
    (w : iutInitialThetaSectionVossPrimeFiber D p) :
    sourceAt D ⟨w.1, w.2.1⟩ ∈ VBadSelectedPaper.selectedFinset D ↔
      w ∈ iutInitialThetaVBadRepresentativePrimeFiberImage D p :=
  (sourceAt_mem_selected_iff_image D ⟨w.1, w.2.1⟩).trans
    (fiber_mem_image_iff D p w).symm

def primeLogTerm (p : ℕ) (w : iutInitialThetaSectionVossPrimeFiber D p) : ℝ :=
  -Real.log (actualPaperRootNorm D (sourceAt D ⟨w.1, w.2.1⟩))

theorem primeLogTerm_pos (p : ℕ) (w : iutInitialThetaSectionVossPrimeFiber D p) :
    0 < primeLogTerm D p w :=
  neg_pos.mpr (Real.log_neg (actualPaperRootNorm_mem_Ioo D _).1
    (actualPaperRootNorm_mem_Ioo D _).2)

theorem primeLogTerm_eq_paperTerm (p : ℕ)
    (w : iutInitialThetaSectionVossPrimeFiber D p) :
    primeLogTerm D p w =
      ((Arithmetic.ramIdx w.1 : ℝ) * Arithmetic.ordp w.1
        ((iutInitialThetaOddSupportTorsionQRootSource D).qroot
          (sourceAt D ⟨w.1, w.2.1⟩))) * Real.log (Arithmetic.residueChar w.1) :=
  actualPaperRootNorm_negLog_eq_paperTerm D _

def omittedPrimeMass (p : ℕ) : ℝ :=
  ∑ w : OmittedPrimeFiber D p, primeLogTerm D p w.1

theorem omittedPrimeMass_nonneg (p : ℕ) : 0 ≤ omittedPrimeMass D p :=
  Finset.sum_nonneg (fun w _ => (primeLogTerm_pos D p w.1).le)

theorem omittedPrimeMass_pos_iff_multiplicity_pos (p : ℕ) :
    0 < omittedPrimeMass D p ↔ 0 < omittedPrimeMultiplicity D p := by
  constructor
  · intro hpos
    by_contra hn
    have hz : Fintype.card (OmittedPrimeFiber D p) = 0 := Nat.eq_zero_of_not_pos hn
    have hempty : (Finset.univ : Finset (OmittedPrimeFiber D p)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w _
      exact (Fintype.card_eq_zero_iff.mp hz).false w
    simp only [omittedPrimeMass, hempty, Finset.sum_empty, lt_self_iff_false] at hpos
  · intro hpos
    obtain ⟨w⟩ := Fintype.card_pos_iff.mp hpos
    exact Finset.sum_pos (fun w _ => primeLogTerm_pos D p w.1) ⟨w, Finset.mem_univ w⟩

noncomputable def omittedSourcePrimeSigmaEquiv :
    ↥(VBadSelectedPaper.fullSelectedFinset D \ VBadSelectedPaper.selectedFinset D) ≃
      Σ p : iutInitialThetaSectionVossPrimeSupportType D, OmittedPrimeFiber D p.1 := by
  refine Equiv.ofBijective (fun t => by
    have hfull := (VBadSelectedPaper.mem_fullSelectedFinset_iff D t.1).mp
      (Finset.mem_sdiff.mp t.2).1
    have hvoss : t.1.1 ∈ iutInitialThetaSectionVoss D := by
      change t.1.1 ∈ iutInitialThetaOddSupportSelectedQRootPlaces D at hfull
      rw [iutInitialThetaOddSupportSelectedQRootPlaces_eq_oddTateSectionPlaces D,
        iutInitialThetaOddTateSectionPlaces_eq_sectionVoss D] at hfull
      exact hfull
    let wf : iutInitialThetaSectionVossPrimeFiber D (Arithmetic.residueChar t.1.1) :=
      ⟨t.1.1, ⟨hvoss, rfl⟩⟩
    have hnot : wf ∉ iutInitialThetaVBadRepresentativePrimeFiberImage D
        (Arithmetic.residueChar t.1.1) := by
      intro h
      exact (Finset.mem_sdiff.mp t.2).2
        ((sourceAt_mem_selected_iff_primeImage D _ wf).mpr h)
    exact ⟨⟨Arithmetic.residueChar t.1.1, ⟨t.1.1, hvoss, rfl⟩⟩, ⟨wf, hnot⟩⟩) ?_
  constructor
  · intro s t h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z => z.2.1.1) h
  · rintro ⟨⟨p, hpSupport⟩, ⟨⟨place, hvoss, hp⟩, homitted⟩⟩
    change Arithmetic.residueChar place = p at hp
    subst p
    let w : VossPlace D := ⟨place, hvoss⟩
    have hnot : sourceAt D w ∉ VBadSelectedPaper.selectedFinset D := by
      intro h
      exact homitted ((sourceAt_mem_selected_iff_primeImage D _
        ⟨place, ⟨hvoss, rfl⟩⟩).mp h)
    refine ⟨⟨sourceAt D w, Finset.mem_sdiff.mpr
      ⟨sourceAt_mem_fullSelected D w, hnot⟩⟩, ?_⟩
    rfl

theorem omittedSourcePrimeSigmaEquiv_logTerm
    (s : ↥(VBadSelectedPaper.fullSelectedFinset D \ VBadSelectedPaper.selectedFinset D)) :
    primeLogTerm D (omittedSourcePrimeSigmaEquiv D s).1.1
        (omittedSourcePrimeSigmaEquiv D s).2.1 =
      -Real.log (actualPaperRootNorm D s.1) := by
  rfl

theorem omittedPaperSum_eq_primeMass_sum :
    VBadSelectedPaper.omittedPaperSum D =
      ∑ p : iutInitialThetaSectionVossPrimeSupportType D, omittedPrimeMass D p.1 := by
  unfold VBadSelectedPaper.omittedPaperSum
  rw [← Finset.sum_coe_sort
    (s := VBadSelectedPaper.fullSelectedFinset D \ VBadSelectedPaper.selectedFinset D)
    (f := fun s => -Real.log (actualPaperRootNorm D s))]
  have h := (omittedSourcePrimeSigmaEquiv D).sum_comp
    (fun z => primeLogTerm D z.1.1 z.2.1)
  simp_rw [omittedSourcePrimeSigmaEquiv_logTerm D] at h
  simpa only [Fintype.sum_sigma, omittedPrimeMass] using h

theorem fullPaperSum_eq_selected_add_primeMass_sum :
    iutInitialThetaSelectedQRootPaperSum D = VBadSelectedPaper.paperSum D +
      ∑ p : iutInitialThetaSectionVossPrimeSupportType D, omittedPrimeMass D p.1 := by
  rw [VBadSelectedPaper.fullPaperSum_eq_selected_add_omitted D,
    omittedPaperSum_eq_primeMass_sum D]

end
end JoshiTeich.Act1Scene1.VossOmittedPrimeMass
