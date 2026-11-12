import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVossOmittedPrimeMass

/-!
source-id: JT-SCENE1-INITIAL-THETA-VOSS-WEIGHTED-OMISSION
source: Joshi III `ss:val-sets-defn`, `ss:weighted-vol` and `eq:weights`;
the actual representative coefficient, full moduli q-pilot accounting,
VBad restriction, and the concrete omitted prime-fiber decomposition.
fidelity: retains the actual representative coefficient in every omitted
q-log term. Computes the full normalized q-pilot as its VBad restriction
plus the prime-indexed weighted omitted mass, bounds that correction by
the existing unweighted omitted paper sum, and characterizes equality by
full odd moduli-support coverage. No coverage is supplied as an input.
boundary: Scene1/Derived; paper representatives, paper volume weights,
mixed-moduli descent and global producer identities remain open.
Original proofs; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1.VossWeightedOmission

open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

def sourceCoefficient (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) : ℝ :=
  if hs : s ∈ VBadSelectedPaper.fullSelectedFinset D then
    iutInitialThetaRepresentativeCoefficient D
      ((iutInitialThetaModuliSelectedSourceEquiv D).symm
        ⟨s, (VBadSelectedPaper.mem_fullSelectedFinset_iff D s).mp hs⟩)
  else 0

theorem sourceCoefficient_fullSourceAt (v : iutInitialThetaOddModSupportFinset D) :
    sourceCoefficient D (VBadSelectedPaper.fullSourceAt D v) =
      iutInitialThetaRepresentativeCoefficient D v := by
  have hs : VBadSelectedPaper.fullSourceAt D v ∈ VBadSelectedPaper.fullSelectedFinset D :=
    Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
  rw [sourceCoefficient, dif_pos hs]
  change iutInitialThetaRepresentativeCoefficient D
    ((iutInitialThetaModuliSelectedSourceEquiv D).symm
      (iutInitialThetaModuliSelectedSourceEquiv D v)) = _
  rw [Equiv.symm_apply_apply]

theorem sourceCoefficient_mem_Ioc_of_mem
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hs : s ∈ VBadSelectedPaper.fullSelectedFinset D) :
    sourceCoefficient D s ∈ Set.Ioc (0 : ℝ) 1 := by
  rw [sourceCoefficient, dif_pos hs]
  exact iutInitialThetaRepresentativeCoefficient_mem_Ioc D _

def weightedLogTerm (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) : ℝ :=
  sourceCoefficient D s * -Real.log (actualPaperRootNorm D s)

theorem weightedLogTerm_pos_of_mem
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hs : s ∈ VBadSelectedPaper.fullSelectedFinset D) :
    0 < weightedLogTerm D s :=
  mul_pos (sourceCoefficient_mem_Ioc_of_mem D s hs).1
    (neg_pos.mpr (Real.log_neg (actualPaperRootNorm_mem_Ioo D s).1
      (actualPaperRootNorm_mem_Ioo D s).2))

theorem fullWeightedSum_eq_fullBaseQPilot :
    (∑ s ∈ VBadSelectedPaper.fullSelectedFinset D, weightedLogTerm D s) =
      iutInitialThetaFullBaseQPilotLogSum D := by
  rw [VBadSelectedPaper.fullSelectedFinset,
    Finset.sum_image (fun _ _ _ _ h => VBadSelectedPaper.fullSourceAt_injective D h),
    iutInitialThetaFullBaseQPilotLogSum_eq_coefficientWeightedPaperSum D]
  apply Finset.sum_congr rfl
  intro v _
  rw [weightedLogTerm, sourceCoefficient_fullSourceAt D v,
    actualPaperRootNorm_negLog_eq_paperTerm]
  rfl

theorem selectedWeightedSum_eq_reference :
    (∑ s ∈ VBadSelectedPaper.selectedFinset D, weightedLogTerm D s) =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  rw [VBadSelectedPaper.selectedFinset,
    Finset.sum_image (fun _ _ _ _ h => VBadSelectedPaper.sourceAt_injective D h)]
  change (∑ v : iutInitialThetaVBadModuliFinset D,
    sourceCoefficient D (VBadSelectedPaper.fullSourceAt D (iutInitialThetaVBadModuliAt D v)) *
      VBadSelectedPaper.paperTerm D v) = _
  simp_rw [sourceCoefficient_fullSourceAt D]
  exact (VBadSelectedPaper.referenceAbsLogQ_eq_coefficientWeightedPaperSum D).symm

def primeWeightedMass (p : ℕ) : ℝ :=
  ∑ w : VossOmittedPrimeFibers.OmittedPrimeFiber D p,
    weightedLogTerm D (VossOmittedPrimeMass.sourceAt D ⟨w.1.1, w.1.2.1⟩)

private theorem fiber_weightedLogTerm_pos (p : ℕ)
    (w : VossOmittedPrimeFibers.OmittedPrimeFiber D p) :
    0 < weightedLogTerm D (VossOmittedPrimeMass.sourceAt D ⟨w.1.1, w.1.2.1⟩) :=
  weightedLogTerm_pos_of_mem D _ (VossOmittedPrimeMass.sourceAt_mem_fullSelected D _)

theorem primeWeightedMass_nonneg (p : ℕ) : 0 ≤ primeWeightedMass D p :=
  Finset.sum_nonneg (fun w _ => (fiber_weightedLogTerm_pos D p w).le)

theorem primeWeightedMass_le_omittedPrimeMass (p : ℕ) :
    primeWeightedMass D p ≤ VossOmittedPrimeMass.omittedPrimeMass D p := by
  apply Finset.sum_le_sum
  intro w _
  change sourceCoefficient D (VossOmittedPrimeMass.sourceAt D ⟨w.1.1, w.1.2.1⟩) *
      VossOmittedPrimeMass.primeLogTerm D p w.1 ≤
    VossOmittedPrimeMass.primeLogTerm D p w.1
  calc
    _ ≤ 1 * VossOmittedPrimeMass.primeLogTerm D p w.1 :=
      mul_le_mul_of_nonneg_right
        (sourceCoefficient_mem_Ioc_of_mem D _
          (VossOmittedPrimeMass.sourceAt_mem_fullSelected D _)).2
        (VossOmittedPrimeMass.primeLogTerm_pos D p w.1).le
    _ = _ := one_mul _

theorem primeWeightedMass_pos_iff_multiplicity_pos (p : ℕ) :
    0 < primeWeightedMass D p ↔
      0 < VossOmittedPrimeFibers.omittedPrimeMultiplicity D p := by
  constructor
  · intro hpos
    exact (VossOmittedPrimeMass.omittedPrimeMass_pos_iff_multiplicity_pos D p).mp
      (hpos.trans_le (primeWeightedMass_le_omittedPrimeMass D p))
  · intro hpos
    obtain ⟨w⟩ := Fintype.card_pos_iff.mp hpos
    exact Finset.sum_pos (fun w _ => fiber_weightedLogTerm_pos D p w)
      ⟨w, Finset.mem_univ w⟩

private theorem sigma_weightedLogTerm
    (s : ↥(VBadSelectedPaper.fullSelectedFinset D \ VBadSelectedPaper.selectedFinset D)) :
    weightedLogTerm D (VossOmittedPrimeMass.sourceAt D
        ⟨(VossOmittedPrimeMass.omittedSourcePrimeSigmaEquiv D s).2.1.1,
          (VossOmittedPrimeMass.omittedSourcePrimeSigmaEquiv D s).2.1.2.1⟩) =
      weightedLogTerm D s.1 := by
  rfl

theorem omittedWeightedSum_eq_primeWeightedMass_sum :
    (∑ s ∈ VBadSelectedPaper.fullSelectedFinset D \ VBadSelectedPaper.selectedFinset D,
      weightedLogTerm D s) =
      ∑ p : iutInitialThetaSectionVossPrimeSupportType D, primeWeightedMass D p.1 := by
  rw [← Finset.sum_coe_sort
    (s := VBadSelectedPaper.fullSelectedFinset D \ VBadSelectedPaper.selectedFinset D)
    (f := weightedLogTerm D)]
  have h := (VossOmittedPrimeMass.omittedSourcePrimeSigmaEquiv D).sum_comp
    (fun z => weightedLogTerm D (VossOmittedPrimeMass.sourceAt D ⟨z.2.1.1, z.2.1.2.1⟩))
  simp_rw [sigma_weightedLogTerm D] at h
  simpa only [Fintype.sum_sigma, primeWeightedMass] using h

theorem fullBaseQPilot_eq_reference_add_primeWeightedMass :
    iutInitialThetaFullBaseQPilotLogSum D =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
          (IutTorsionQRootSource.iutInitialThetaQPilotData D) +
        ∑ p : iutInitialThetaSectionVossPrimeSupportType D, primeWeightedMass D p.1 := by
  rw [← fullWeightedSum_eq_fullBaseQPilot D, ← selectedWeightedSum_eq_reference D,
    ← omittedWeightedSum_eq_primeWeightedMass_sum D]
  exact (Finset.sum_sdiff (f := weightedLogTerm D)
    (VBadSelectedPaper.selectedFinset_subset_fullSelectedFinset D)).symm.trans (add_comm _ _)

theorem fullBase_sub_reference_eq_primeWeightedMass_sum :
    iutInitialThetaFullBaseQPilotLogSum D -
        JoshiTeich.ReferenceIut.QPilotData.absLogQ
          (IutTorsionQRootSource.iutInitialThetaQPilotData D) =
      ∑ p : iutInitialThetaSectionVossPrimeSupportType D, primeWeightedMass D p.1 := by
  rw [fullBaseQPilot_eq_reference_add_primeWeightedMass D]
  ring

theorem fullBase_sub_reference_mem_Icc :
    iutInitialThetaFullBaseQPilotLogSum D -
        JoshiTeich.ReferenceIut.QPilotData.absLogQ
          (IutTorsionQRootSource.iutInitialThetaQPilotData D) ∈
      Set.Icc (0 : ℝ) (VBadSelectedPaper.omittedPaperSum D) := by
  rw [fullBase_sub_reference_eq_primeWeightedMass_sum D,
    VossOmittedPrimeMass.omittedPaperSum_eq_primeMass_sum D]
  exact ⟨Finset.sum_nonneg (fun p _ => primeWeightedMass_nonneg D p.1),
    Finset.sum_le_sum (fun p _ => primeWeightedMass_le_omittedPrimeMass D p.1)⟩

theorem reference_eq_fullBase_iff_coverage :
    JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) =
      iutInitialThetaFullBaseQPilotLogSum D ↔
        iutInitialThetaVBadModuliFinset D = iutInitialThetaOddModSupportFinset D := by
  constructor
  · intro heq
    by_contra hmissing
    obtain ⟨p, hp, hgap⟩ := VossOmittedPrimeFibers.exists_primeMultiplicity_gap_of_missing D hmissing
    have hpos := (primeWeightedMass_pos_iff_multiplicity_pos D p).mpr
      ((VossOmittedPrimeFibers.primeMultiplicity_lt_iff_omitted_pos D p).mp hgap)
    let q : iutInitialThetaSectionVossPrimeSupportType D := ⟨p, hp⟩
    have hsingle := Finset.single_le_sum
      (f := fun r : iutInitialThetaSectionVossPrimeSupportType D => primeWeightedMass D r.1)
      (fun r _ => primeWeightedMass_nonneg D r.1) (Finset.mem_univ q)
    have hzero : (∑ r : iutInitialThetaSectionVossPrimeSupportType D,
        primeWeightedMass D r.1) = 0 := by
      have h := fullBaseQPilot_eq_reference_add_primeWeightedMass D
      linarith
    rw [hzero] at hsingle
    exact (not_lt_of_ge hsingle) hpos
  · intro hcover
    have h := fullBase_sub_reference_mem_Icc D
    rw [(VBadSelectedPaper.omittedPaperSum_eq_zero_iff_coverage D).mpr hcover] at h
    rcases h with ⟨hlo, hhi⟩
    linarith

end
end JoshiTeich.Act1Scene1.VossWeightedOmission
