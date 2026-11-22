import Solutions.Source_ReferenceIutCor312RepresentativePadicProduct
import Solutions.Source_ReferenceIutConcreteLocalOrder
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalPadicPaperLog
import ArithmeticTeichmullerSpaces.Prologue.Audit.Checks
import ArithmeticTeichmullerSpaces.Prologue.Audit.ImportAudit
import ArithmeticTeichmullerSpaces.Act1Scene1
import ArithmeticTeichmullerSpaces.Prologue.Audit.AxiomAudit

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.ThetaLocalData

open NumberField JoshiTeich.Act1Scene1
open scoped BigOperators Valued

universe u v

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {D : InitialThetaData AG TG} {LT : LocalTheory.{u, v} D.Kt}

local instance comparisonLogPrime {K : Type*} [Field K] [NumberField K] (w : FinitePlace K) :
    Fact (JoshiTeich.Prologue.Arithmetic.residueChar w).Prime :=
  LocalCompletion.selectedPrime w

/-- The p*-divided ordinary logarithm associated with the chosen Tate root. -/
noncomputable def paperNormalizedQRootLog (TL : ThetaLocalData D LT) (s : FinitePlace D.Kt) :
    LocalCompletion.completionAt D.Kt s :=
  letI := LocalCompletion.completionCharZero s
  LocalPadicLog.paperNormalizedLog (JoshiTeich.Prologue.Arithmetic.residueChar s) (TL.qroot s)

private theorem norm_paperNormalizedQRootLog_eq_qroot
    (TL : ThetaLocalData D LT) (s : FinitePlace D.Kt) :
    ‖TL.paperNormalizedQRootLog s‖ = ‖TL.qroot s‖ := by
  let _ := LocalCompletion.completionCharZero s
  let p := JoshiTeich.Prologue.Arithmetic.residueChar s
  have hp : p.Prime := JoshiTeich.Prologue.Arithmetic.residueChar_prime s
  have hpNorm : ‖(p : LocalCompletion.completionAt D.Kt s)‖ < 1 := by
    have h := LocalCompletion.norm_natCast_prime_lt_one (p := p) (w := s) rfl
    rwa [← FinitePlace.embedding_apply, map_natCast] at h
  have hroot : ‖TL.qroot s‖ ≤ 1 :=
    LocalConstruct.norm_le_one_of_ordp_nonneg (TL.ordp_qroot_nonneg s)
  exact LocalPadicLog.norm_paperNormalizedLog hp hpNorm hroot

private theorem norm_standardPaperNormalizedQRootLog_eq_qroot
    (TL : ThetaLocalData D LT) (s : FinitePlace D.Kt) :
    ‖completionInPadicComplex s (TL.paperNormalizedQRootLog s)‖ = ‖TL.qrootInPadicComplex s‖ := by
  have hpow : ‖completionInPadicComplex s (TL.paperNormalizedQRootLog s)‖ ^
      JoshiTeich.Prologue.Arithmetic.localDeg s = ‖TL.paperNormalizedQRootLog s‖ :=
    completionInPadicComplex_norm_pow s (TL.paperNormalizedQRootLog s)
  have hqpow : ‖TL.qrootInPadicComplex s‖ ^ JoshiTeich.Prologue.Arithmetic.localDeg s =
      ‖TL.qroot s‖ :=
    completionInPadicComplex_norm_pow s (TL.qroot s)
  apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _)
    (JoshiTeich.Prologue.Arithmetic.localDeg_pos s).ne').mp
  exact hpow.trans ((norm_paperNormalizedQRootLog_eq_qroot TL s).trans hqpow.symm)

/-- A comparison value at each selected place gives the standard-norm factor
once its equality with the p*-divided ordinary logarithm is supplied. -/
theorem sectionQRootProduct_eq_comparisonLogProduct
    (TL : ThetaLocalData D LT) (QI : QPilotInputs D)
    (logValue : (w : QI.badModuliFinset) →
      LocalCompletion.completionAt D.Kt (D.localData.sect.sectFin w.1))
    (hLogValue : ∀ w, logValue w = TL.paperNormalizedQRootLog (D.localData.sect.sectFin w.1))
    (exponent : ℝ) :
    let M := ↥(fieldOfModuli D.F D.E)
    TL.sectionQRootProduct QI exponent =
      ∏ w ∈ QI.badModuliFinset.attach,
        ‖completionInPadicComplex (D.localData.sect.sectFin w.1) (logValue w)‖ ^
          (exponent * placeWeight M w.1) := by
  dsimp only
  rw [sectionQRootProduct_eq_padicComplexProduct, ← Finset.prod_attach]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [hLogValue w, norm_standardPaperNormalizedQRootLog_eq_qroot TL]

/-- The comparison-log factors with the standard-point square exponents
give the sum of the finite packet log volumes divided by `m²`. -/
theorem log_normalized_sectionComparisonLogProduct_eq_sum_finite_packetVol
    (hModuli : @algebraMap ↥(fieldOfModuli D.F D.E) D.Kt _ _ D.algebraModK =
      (algebraMap D.F D.Kt).comp (algebraMap ↥(fieldOfModuli D.F D.E) D.F))
    (TL : ThetaLocalData D (LocalConstruct.concreteLocalTheory (K := D.Kt)))
    (QI : QPilotInputs D)
    (logValue : (w : QI.badModuliFinset) →
      LocalCompletion.completionAt D.Kt (D.localData.sect.sectFin w.1))
    (hLogValue : ∀ w, logValue w = TL.paperNormalizedQRootLog (D.localData.sect.sectFin w.1)) :
    let m := (D.ℓ - 1) / 2
    let M := ↥(fieldOfModuli D.F D.E)
    let R := TL.rhsData
    Real.log (∏ i : Fin m, ∏ w ∈ QI.badModuliFinset.attach,
      ‖completionInPadicComplex (D.localData.sect.sectFin w.1) (logValue w)‖ ^
        ((((i.1 + 1 : ℕ) : ℝ) / (m : ℝ)) ^ 2 * placeWeight M w.1)) =
      (∑ i : Fin m, ∑ p ∈ TL.badChars.attach,
        let q := RationalPlace.finite ⟨p.1, TL.badChars_prime p.1 p.2⟩
        R.vol.packetVol i q ((R.thetaHull i).region q)) / (m : ℝ) ^ 2 := by
  simpa only [sectionQRootProduct_eq_comparisonLogProduct TL QI logValue hLogValue] using
    log_normalized_sectionQRootProduct_eq_sum_finite_packetVol hModuli TL QI

end AbcAdaptation.Reference.Iut.ThetaLocalData

#print axioms AbcAdaptation.Reference.Iut.ThetaLocalData.completionInPadicComplex
#print axioms AbcAdaptation.Reference.Iut.ThetaLocalData.completionInPadicComplex_norm_pow
#print axioms AbcAdaptation.Reference.Iut.ThetaLocalData.qrootInPadicComplex
#print axioms AbcAdaptation.Reference.Iut.ThetaLocalData.sectionQRootProduct_eq_padicComplexProduct
#print axioms AbcAdaptation.Reference.Iut.ThetaLocalData.log_normalized_sectionPadicComplexProduct_eq_sum_finite_packetVol
#print axioms AbcAdaptation.Reference.Iut.ThetaLocalData.paperNormalizedQRootLog
#print axioms AbcAdaptation.Reference.Iut.ThetaLocalData.sectionQRootProduct_eq_comparisonLogProduct
#print axioms AbcAdaptation.Reference.Iut.ThetaLocalData.log_normalized_sectionComparisonLogProduct_eq_sum_finite_packetVol
