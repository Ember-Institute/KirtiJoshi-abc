import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaReferenceCoefficientOrdinaryWeight
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCorrectionCostCoverage
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadSelectedPaperAccounting

/-!
source-id: JT-SCENE1-ACTUAL-REFERENCE-GLOBAL-NEGATIVE-MARGIN
source: actual VBad/full-support coverage, coefficient-weighted reference
accounting and ordinary corrected-cost sums; Joshi III 1028--1055,
eq:weights and 3520--3574.
fidelity: under full VBad coverage and a source residue-degree upper bound,
the reference q-pilot is strictly smaller than the ordinary corrected cost.
This is a conditional negative result for the current ordinary-log route;
it does not construct actual data satisfying the degree upper bound and does
not refute the paper's theorem with a different normalization.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance globalNegativePrime (v : iutInitialThetaOddModSupportFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩

theorem vbadPaperTerm_eq_selectedPaperTerm_of_coverage
    (hcover : iutInitialThetaVBadModuliFinset D = iutInitialThetaOddModSupportFinset D)
    (v : iutInitialThetaOddModSupportFinset D) :
    VBadSelectedPaper.paperTerm D
      ⟨v.1, hcover.symm ▸ v.2⟩ = selectedPaperTerm D v := by
  rfl

theorem referenceAbsLogQ_eq_full_coefficient_sum_of_coverage
    (hcover : iutInitialThetaVBadModuliFinset D = iutInitialThetaOddModSupportFinset D) :
    JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) =
      ∑ v : iutInitialThetaOddModSupportFinset D,
        iutInitialThetaRepresentativeCoefficient D v * selectedPaperTerm D v := by
  have href := VBadSelectedPaper.referenceAbsLogQ_eq_coefficientWeightedPaperSum D
  have htoOdd (v : iutInitialThetaVBadModuliFinset D) :
      v.1 ∈ iutInitialThetaOddModSupportFinset D := by
    rw [← hcover]
    exact v.2
  have htoVBad (v : iutInitialThetaOddModSupportFinset D) :
      v.1 ∈ iutInitialThetaVBadModuliFinset D := by
    rw [hcover]
    exact v.2
  calc
    _ = ∑ v : iutInitialThetaVBadModuliFinset D,
        iutInitialThetaRepresentativeCoefficient D (iutInitialThetaVBadModuliAt D v) *
          VBadSelectedPaper.paperTerm D v := href
    _ = ∑ v : iutInitialThetaOddModSupportFinset D,
        iutInitialThetaRepresentativeCoefficient D v * selectedPaperTerm D v := by
      apply Finset.sum_bij (fun v _ =>
        (⟨v.1, htoOdd v⟩ : iutInitialThetaOddModSupportFinset D))
      · intro v hv; exact Finset.mem_univ _
      · intro v hv w hw h
        have hp : v.1 = w.1 := congrArg (fun x : iutInitialThetaOddModSupportFinset D => x.1) h
        exact Subtype.ext hp
      · intro w hw; exact ⟨⟨w.1, htoVBad w⟩, Finset.mem_univ _, rfl⟩
      · intro v hv
        rfl

theorem referenceAbsLogQ_lt_correctedCost_of_coverage_of_sourceInertDeg_le
    (hcover : iutInitialThetaVBadModuliFinset D = iutInitialThetaOddModSupportFinset D)
    (hdeg : ∀ v : iutInitialThetaOddModSupportFinset D,
      Arithmetic.inertDeg (FullSupportPaperWeightedHull.selected D v).1 ≤
        Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) :
    JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) <
      FullSupportPaperWeightedHull.weightedPaperSum D - Real.log (correction D 1) := by
  rw [referenceAbsLogQ_eq_full_coefficient_sum_of_coverage D hcover,
    correctedCost_eq_sum D]
  have hlt (v : iutInitialThetaOddModSupportFinset D) :
      iutInitialThetaRepresentativeCoefficient D v * selectedPaperTerm D v <
        correctedLocalCost D v := by
    have hm := referenceLocalMargin_neg_of_sourceInertDeg_le_moduliDegree D v (hdeg v)
    unfold referenceLocalMargin at hm
    linarith
  obtain ⟨v0, hv0⟩ := D.global.bad_nonempty
  let v₀ : iutInitialThetaOddModSupportFinset D :=
    ⟨v0, (iutInitialThetaOddModSupport_finite D).mem_toFinset.mpr
      (iutInitialThetaVBad_subset_VBadOdd D hv0)⟩
  exact Finset.sum_lt_sum (fun v _ => (hlt v).le)
    ⟨v₀, Finset.mem_univ _, hlt v₀⟩

end
end JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
