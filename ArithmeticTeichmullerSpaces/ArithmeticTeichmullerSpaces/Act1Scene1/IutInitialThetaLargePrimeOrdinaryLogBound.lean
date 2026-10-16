import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCorrectionCostCoverage
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaLargePrimeSupport

/-!
source-id: JT-SCENE1-ACTUAL-LARGE-PRIME-ORDINARY-LOG-BOUND
source: maximal prime-to-ell VBad, the finite multiplicative residue bound,
and original ordinary-log correction costs; Joshi III Section 3 and
3520--3574, 3624--3631.
fidelity: on the existing large-prime source route, full moduli coverage
and zero complementary cost are derived. The remaining moduli ramification
condition yields a positive global margin and strict ordinary-log collation
bound; no separate support equality or correction-cost budget is input.
boundary: Scene1/Derived; no paper thetaVolume or BK/untilt identification.
-/

namespace JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
open JoshiTeich.Prologue
open scoped Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance largePrimeOrdinaryPrime (v : iutInitialThetaOddModSupportFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩
variable (hVBad : D.VBad = {v | v ∈ IutOddMultiplicativeModSupport D ∧
  Arithmetic.residueChar v ≠ D.prime.ℓ})
variable (hLarge : iutMultiplicativeResidueBound D.E < D.prime.ℓ)
include hVBad hLarge

theorem vbad_moduli_coverage_of_largePrime :
    iutInitialThetaVBadModuliFinset D = iutInitialThetaOddModSupportFinset D := by
  apply (complementCorrectionCost_eq_zero_iff_coverage D).mp
  apply (complementCorrectionCost_eq_zero_iff_all_mem_vbad D).mpr
  intro v
  have hv : v.1 ∈ IutOddMultiplicativeModSupport D := by
    rw [iutInitialThetaOddMultiplicativeModSupport_eq_VBadOdd]
    exact (iutInitialThetaOddModSupport_finite D).mem_toFinset.mp v.2
  obtain ⟨w, hw⟩ := hv.2.1
  have hwv : Ideal.LiesOver w.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal := hw
  have hbound := iutMultiplicative_residueChar_le_bound D.E w (hv.2.2 w hw)
  rw [Arithmetic.residueChar_eq_of_liesOver hwv] at hbound
  rw [hVBad]
  exact ⟨hv, by omega⟩

theorem complementCorrectionCost_eq_zero_of_largePrime : complementCorrectionCost D = 0 :=
  (complementCorrectionCost_eq_zero_iff_coverage D).mpr
    (vbad_moduli_coverage_of_largePrime D hVBad hLarge)

theorem globalArithmeticMargin_pos_of_largePrime
    (he : ∀ v : iutInitialThetaOddModSupportFinset D, Arithmetic.ramIdx v.1 ≤ 2) :
    0 < globalArithmeticMargin D :=
  globalArithmeticMargin_pos_of_full_coverage D (vbad_moduli_coverage_of_largePrime D hVBad hLarge)
    (fun v _ => he v)

theorem correctedCost_lt_selectedPaperSum_of_largePrime
    (he : ∀ v : iutInitialThetaOddModSupportFinset D, Arithmetic.ramIdx v.1 ≤ 2) :
    FullSupportPaperWeightedHull.weightedPaperSum D - Real.log (correction D 1) <
      iutInitialThetaSelectedQRootPaperSum D :=
  correctedCost_lt_selectedPaperSum_of_full_coverage D
    (vbad_moduli_coverage_of_largePrime D hVBad hLarge) (fun v _ => he v)

variable (n : ℕ) {κ : Type*}
variable (C : ∀ v : iutInitialThetaOddModSupportFinset D, κ → Set (packet D n v).Tensor)
variable (hw : ∀ v, witness D n v ∈ ⋃ k, C v k)
variable (hunit : ∀ v k, C v k ⊆ (packet D n v).normalization)

include hw hunit in
theorem ordinary_collation_averageAbsLog_lt_selectedPaperSum_of_largePrime
    (hn : 0 < n)
    (he : ∀ v : iutInitialThetaOddModSupportFinset D, Arithmetic.ramIdx v.1 ≤ 2) :
    (1 / (n : ℝ)) * |Real.log (FullSupportWitnessHull.volume D n C)| <
      iutInitialThetaSelectedQRootPaperSum D :=
  (ordinary_collation_averageAbsLog_le_correctedCost D n C hw hunit hn).trans_lt
    (correctedCost_lt_selectedPaperSum_of_largePrime D hVBad hLarge he)

end
end JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
