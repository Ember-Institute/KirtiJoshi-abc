import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadRootProductContracting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRepresentativeRamificationGap
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPaperRootHaarBridge

/-!
source-id: JT-SCENE1-INITIAL-THETA-VBAD-SELECTED-PAPER-ACCOUNTING
source: actual VBad section restriction, representative coefficient and
paper-corrected root norm; Joshi III section/locus definitions (1028--1055).
fidelity: constructs a bijective finite carrier of selected roots over exactly
VBad and computes the reference q-pilot as its coefficient-weighted paper
sum. It does not identify VBad with the complete odd semistable locus.
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

def sourceAt (v : iutInitialThetaVBadModuliFinset D) :
    (iutInitialThetaOddSupportTorsionQRootSource D).badFinset :=
  (iutInitialThetaModuliSelectedSourceEquiv D (iutInitialThetaVBadModuliAt D v)).1

theorem sourceAt_injective : Function.Injective (sourceAt D) := by
  intro v w h
  have hfull := (iutInitialThetaModuliSelectedSourceEquiv D).injective (Subtype.ext h)
  exact Subtype.ext (congrArg (fun x : iutInitialThetaOddModSupportFinset D => x.1) hfull)

theorem sourceAt_liesOver (v : iutInitialThetaVBadModuliFinset D) :
    Ideal.LiesOver (sourceAt D v).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal :=
  iutInitialThetaModuliSelectedSource_liesOver D (iutInitialThetaVBadModuliAt D v)

def selectedFinset : Finset (iutInitialThetaOddSupportTorsionQRootSource D).badFinset :=
  Finset.univ.image (sourceAt D)

theorem mem_selectedFinset_iff (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    s ∈ selectedFinset D ↔ ∃ v : iutInitialThetaVBadModuliFinset D, sourceAt D v = s := by
  simp only [selectedFinset, Finset.mem_image, Finset.mem_univ, true_and]

def sourceEquiv : iutInitialThetaVBadModuliFinset D ≃ ↥(selectedFinset D) :=
  Equiv.ofBijective (fun v => ⟨sourceAt D v, (mem_selectedFinset_iff D _).mpr ⟨v, rfl⟩⟩)
    ⟨fun _ _ h => sourceAt_injective D
      (congrArg (fun x : ↥(selectedFinset D) => x.1) h), by
      intro s
      obtain ⟨v, hv⟩ := (mem_selectedFinset_iff D s.1).mp s.2
      exact ⟨v, Subtype.ext hv⟩⟩

theorem selectedFinset_card : (selectedFinset D).card = (iutInitialThetaVBadModuliFinset D).card := by
  simpa only [Fintype.card_coe] using (Fintype.card_congr (sourceEquiv D)).symm

theorem selectedFinset_subset_fullSelected (s : ↥(selectedFinset D)) :
    s.1 ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D := by
  obtain ⟨v, hv⟩ := (mem_selectedFinset_iff D s.1).mp s.2
  rw [← hv]
  exact (iutInitialThetaModuliSelectedSourceEquiv D (iutInitialThetaVBadModuliAt D v)).2

def paperTerm (v : iutInitialThetaVBadModuliFinset D) : ℝ :=
  -Real.log (actualPaperRootNorm D (sourceAt D v))

def paperSum : ℝ := ∑ v : iutInitialThetaVBadModuliFinset D, paperTerm D v

def rootProduct : ℝ := ∏ s : ↥(selectedFinset D), actualPaperRootNorm D s.1

theorem paperTerm_pos (v : iutInitialThetaVBadModuliFinset D) : 0 < paperTerm D v :=
  neg_pos.mpr (Real.log_neg (actualPaperRootNorm_mem_Ioo D _).1
    (actualPaperRootNorm_mem_Ioo D _).2)

theorem paperSum_eq_selectedRootLogSum :
    paperSum D = ∑ s : ↥(selectedFinset D), -Real.log (actualPaperRootNorm D s.1) :=
  (sourceEquiv D).sum_comp (fun s => -Real.log (actualPaperRootNorm D s.1))

theorem rootProduct_pos : 0 < rootProduct D :=
  Finset.prod_pos fun s _ => (actualPaperRootNorm_mem_Ioo D s.1).1

theorem negLog_rootProduct_eq_paperSum : -Real.log (rootProduct D) = paperSum D := by
  rw [rootProduct, Real.log_prod (fun s _ => (actualPaperRootNorm_mem_Ioo D s.1).1.ne'),
    ← Finset.sum_neg_distrib, ← paperSum_eq_selectedRootLogSum]

theorem referenceAbsLogQ_eq_coefficientWeightedPaperSum :
    JoshiTeich.ReferenceIut.QPilotData.absLogQ (IutTorsionQRootSource.iutInitialThetaQPilotData D) =
      ∑ v : iutInitialThetaVBadModuliFinset D,
        iutInitialThetaRepresentativeCoefficient D (iutInitialThetaVBadModuliAt D v) * paperTerm D v := by
  rw [iutInitialThetaReferenceAbsLogQ_eq_VBadModuliJLogSum, Finset.sum_div, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro v _
  rw [paperTerm, actualPaperRootNorm_negLog_eq_paperTerm]
  exact iutInitialThetaModuliJLogTerm_eq_coefficient_mul_selectedPaperTerm D
    (iutInitialThetaVBadModuliAt D v)

theorem referenceAbsLogQ_lt_paperSum :
    JoshiTeich.ReferenceIut.QPilotData.absLogQ (IutTorsionQRootSource.iutInitialThetaQPilotData D) <
      paperSum D := by
  obtain ⟨v, hv⟩ := D.global.bad_nonempty
  let v₀ : iutInitialThetaVBadModuliFinset D :=
    ⟨v, (mem_iutInitialThetaVBadModuliFinset_iff D v).mpr hv⟩
  have hlt (w : iutInitialThetaVBadModuliFinset D) :
      iutInitialThetaRepresentativeCoefficient D (iutInitialThetaVBadModuliAt D w) *
        paperTerm D w < paperTerm D w := by
    have h := iutInitialThetaRepresentativeCoefficient_lt_one_on_vbad D
      (iutInitialThetaVBadModuliAt D w) ((mem_iutInitialThetaVBadModuliFinset_iff D w.1).mp w.2)
    simpa only [one_mul] using mul_lt_mul_of_pos_right h (paperTerm_pos D w)
  rw [referenceAbsLogQ_eq_coefficientWeightedPaperSum, paperSum]
  exact Finset.sum_lt_sum (fun w _ => (hlt w).le) ⟨v₀, Finset.mem_univ _, hlt v₀⟩

theorem rootProduct_lt_normalizedVBadRootProduct :
    rootProduct D < iutInitialThetaNormalizedVBadRelativeQRootProduct D := by
  have h := referenceAbsLogQ_lt_paperSum D
  rw [← iutInitialThetaNormalizedVBadRelativeQRootProduct_negLog_eq_referenceAbsLogQ D,
    ← negLog_rootProduct_eq_paperSum D] at h
  exact (Real.log_lt_log_iff (rootProduct_pos D)
    (iutInitialThetaNormalizedVBadRelativeQRootProduct_pos D)).mp (neg_lt_neg_iff.mp h)

end
end JoshiTeich.Act1Scene1.VBadSelectedPaper
