import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadSelectedPaperAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedPaperRootNormProduct

/-!
source-id: JT-SCENE1-INITIAL-THETA-VBAD-SELECTED-SUPPORT-DEFECT
source: Joshi III complete section odd semistable locus (1028--1055) and
actual VBad restriction of the selected roots.
fidelity: computes the exact omitted positive q-log contribution and proves
it vanishes exactly when VBad covers the complete odd moduli support. Carrier
equality, sum equality and root product equality have the same criterion.
No coverage certificate or specific counterexample is assumed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.VBadSelectedPaper
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

def fullSourceAt (v : iutInitialThetaOddModSupportFinset D) :
    (iutInitialThetaOddSupportTorsionQRootSource D).badFinset :=
  (iutInitialThetaModuliSelectedSourceEquiv D v).1

theorem fullSourceAt_injective : Function.Injective (fullSourceAt D) :=
  fun _ _ h => (iutInitialThetaModuliSelectedSourceEquiv D).injective (Subtype.ext h)

def fullSelectedFinset : Finset (iutInitialThetaOddSupportTorsionQRootSource D).badFinset :=
  Finset.univ.image (fullSourceAt D)

theorem mem_fullSelectedFinset_iff (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    s ∈ fullSelectedFinset D ↔ s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D := by
  constructor
  · intro hs
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hs
    exact (iutInitialThetaModuliSelectedSourceEquiv D v).2
  · intro hs
    obtain ⟨v, hv⟩ := (iutInitialThetaModuliSelectedSourceEquiv D).surjective ⟨s, hs⟩
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, congrArg Subtype.val hv⟩

theorem selectedFinset_subset_fullSelectedFinset : selectedFinset D ⊆ fullSelectedFinset D :=
  fun _ hs => (mem_fullSelectedFinset_iff D _).mpr (selectedFinset_subset_fullSelected D ⟨_, hs⟩)

theorem selectedFinset_eq_fullSelectedFinset_iff_coverage :
    selectedFinset D = fullSelectedFinset D ↔
      iutInitialThetaVBadModuliFinset D = iutInitialThetaOddModSupportFinset D := by
  constructor
  · intro heq
    have hc := congrArg Finset.card heq
    rw [selectedFinset_card, fullSelectedFinset,
      Finset.card_image_of_injective _ (fullSourceAt_injective D),
      Finset.card_univ, Fintype.card_coe] at hc
    exact Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) hc.ge
  · intro hcover
    apply Finset.Subset.antisymm (selectedFinset_subset_fullSelectedFinset D)
    intro s hs
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hs
    let w : iutInitialThetaVBadModuliFinset D := ⟨v.1, hcover.symm ▸ v.2⟩
    exact (mem_selectedFinset_iff D s).mpr ⟨w, hv⟩

def omittedPaperSum : ℝ :=
  ∑ s ∈ fullSelectedFinset D \ selectedFinset D, -Real.log (actualPaperRootNorm D s)

private theorem rootLogTerm_pos (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    0 < -Real.log (actualPaperRootNorm D s) :=
  neg_pos.mpr (Real.log_neg (actualPaperRootNorm_mem_Ioo D s).1 (actualPaperRootNorm_mem_Ioo D s).2)

theorem fullPaperSum_eq_sum_fullSelected :
    iutInitialThetaSelectedQRootPaperSum D =
      ∑ s ∈ fullSelectedFinset D, -Real.log (actualPaperRootNorm D s) := by
  rw [fullSelectedFinset, Finset.sum_image (fun _ _ _ _ h => fullSourceAt_injective D h)]
  simp_rw [actualPaperRootNorm_negLog_eq_paperTerm]
  let S := {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
    s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
  letI : Fintype S := (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
  exact ((iutInitialThetaModuliSelectedSourceEquiv D).sum_comp
    (fun s : S => ((Arithmetic.ramIdx s.1.1 : ℝ) * Arithmetic.ordp s.1.1
      ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s.1)) *
        Real.log (Arithmetic.residueChar s.1.1))).symm

theorem fullPaperSum_eq_selected_add_omitted :
    iutInitialThetaSelectedQRootPaperSum D = paperSum D + omittedPaperSum D := by
  rw [fullPaperSum_eq_sum_fullSelected, paperSum_eq_selectedRootLogSum,
    Finset.sum_coe_sort (s := selectedFinset D) (f := fun s => -Real.log (actualPaperRootNorm D s))]
  exact (Finset.sum_sdiff (f := fun s => -Real.log (actualPaperRootNorm D s))
    (selectedFinset_subset_fullSelectedFinset D)).symm.trans (add_comm _ _)

theorem omittedPaperSum_nonneg : 0 ≤ omittedPaperSum D :=
  Finset.sum_nonneg fun s _ => (rootLogTerm_pos D s).le

theorem omittedPaperSum_eq_zero_iff_coverage :
    omittedPaperSum D = 0 ↔
      iutInitialThetaVBadModuliFinset D = iutInitialThetaOddModSupportFinset D := by
  rw [← selectedFinset_eq_fullSelectedFinset_iff_coverage D]
  constructor
  · intro hz
    apply Finset.Subset.antisymm (selectedFinset_subset_fullSelectedFinset D)
    intro s hs
    by_contra hnot
    have h := Finset.single_le_sum (f := fun t => -Real.log (actualPaperRootNorm D t))
      (s := fullSelectedFinset D \ selectedFinset D) (fun t _ => (rootLogTerm_pos D t).le)
      (Finset.mem_sdiff.mpr ⟨hs, hnot⟩)
    change -Real.log (actualPaperRootNorm D s) ≤ omittedPaperSum D at h
    rw [hz] at h
    exact (not_lt_of_ge h) (rootLogTerm_pos D s)
  · intro heq
    simp only [omittedPaperSum, heq, Finset.sdiff_self, Finset.sum_empty]

theorem paperSum_le_fullPaperSum : paperSum D ≤ iutInitialThetaSelectedQRootPaperSum D := by
  rw [fullPaperSum_eq_selected_add_omitted]
  exact le_add_of_nonneg_right (omittedPaperSum_nonneg D)

theorem paperSum_eq_fullPaperSum_iff_coverage :
    paperSum D = iutInitialThetaSelectedQRootPaperSum D ↔
      iutInitialThetaVBadModuliFinset D = iutInitialThetaOddModSupportFinset D := by
  rw [fullPaperSum_eq_selected_add_omitted, ← omittedPaperSum_eq_zero_iff_coverage]
  exact ⟨fun h => (add_left_cancel (by simpa only [add_zero] using h.symm)),
    fun h => by rw [h, add_zero]⟩

theorem paperSum_lt_fullPaperSum_of_missing_place
    (hmissing : iutInitialThetaVBadModuliFinset D ≠ iutInitialThetaOddModSupportFinset D) :
    paperSum D < iutInitialThetaSelectedQRootPaperSum D := by
  rw [fullPaperSum_eq_selected_add_omitted]
  exact lt_add_of_pos_right _ (lt_of_le_of_ne (omittedPaperSum_nonneg D)
    (Ne.symm (fun h => hmissing ((omittedPaperSum_eq_zero_iff_coverage D).mp h))))

theorem rootProduct_eq_fullRootProduct_iff_coverage :
    rootProduct D = actualSelectedPaperRootNormProduct D ↔
      iutInitialThetaVBadModuliFinset D = iutInitialThetaOddModSupportFinset D := by
  rw [← paperSum_eq_fullPaperSum_iff_coverage D,
    ← negLog_rootProduct_eq_paperSum D, ← actualSelectedPaperRootNormProduct_negLog_eq_paperSum D,
    neg_inj]
  exact ⟨congrArg Real.log, Real.log_injOn_pos (rootProduct_pos D)
    (actualSelectedPaperRootNormProduct_mem_Ioo D).1⟩

end
end JoshiTeich.Act1Scene1.VBadSelectedPaper
