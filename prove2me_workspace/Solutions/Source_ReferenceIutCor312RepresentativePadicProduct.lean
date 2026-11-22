import Solutions.Source_ReferenceIutCor312RepresentativeProduct
import Solutions.Source_TripodRelativeDegreeTower
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionAlgebraicPadicNorm

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.ThetaLocalData

open NumberField JoshiTeich.Act1Scene1
open scoped BigOperators

universe u v

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {D : InitialThetaData AG TG} {LT : LocalTheory.{u, v} D.Kt}

local instance padicComplexPrime {K : Type*} [Field K] [NumberField K] (w : FinitePlace K) :
    Fact (JoshiTeich.Prologue.Arithmetic.residueChar w).Prime :=
  LocalCompletion.selectedPrime w

section Completion

variable {K : Type u} [Field K] [NumberField K] (w : FinitePlace K)

private noncomputable def completionInAlgebraicClosure
    (x : LocalCompletion.completionAt K w) : LocalCompletion.AlgebraicCompletion w :=
  letI := LocalCompletion.completionNontrivialNorm w
  algebraMap (LocalCompletion.completionAt K w) (LocalCompletion.AlgebraicCompletion w) x

private theorem completionInAlgebraicClosure_norm
    (x : LocalCompletion.completionAt K w) :
    ‖completionInAlgebraicClosure w x‖ = ‖x‖ := by
  let _ := LocalCompletion.completionNontrivialNorm w
  let _ := LocalCompletion.completionComplete w
  let _ := LocalCompletion.completionUltrametric w
  exact norm_algebraMap' (LocalCompletion.AlgebraicCompletion w) x

/-- The map from a finite completion with its Haar norm into standard `ℂ_p`. -/
noncomputable def completionInPadicComplex
    (x : LocalCompletion.completionAt K w) :
    PadicComplex (JoshiTeich.Prologue.Arithmetic.residueChar w) :=
  (LocalCompletion.padicAlgClEquiv w (completionInAlgebraicClosure w x) :
    PadicComplex (JoshiTeich.Prologue.Arithmetic.residueChar w))

theorem completionInPadicComplex_norm_pow
    (x : LocalCompletion.completionAt K w) :
    ‖completionInPadicComplex w x‖ ^ JoshiTeich.Prologue.Arithmetic.localDeg w = ‖x‖ := by
  let a : LocalCompletion.AlgebraicCompletion w := completionInAlgebraicClosure w x
  let y : PadicAlgCl (JoshiTeich.Prologue.Arithmetic.residueChar w) :=
    LocalCompletion.padicAlgClEquiv w a
  have hcoe : ‖(y : PadicComplex (JoshiTeich.Prologue.Arithmetic.residueChar w))‖ = ‖y‖ :=
    UniformSpace.Completion.norm_coe y
  have hpow : ‖y‖ ^ JoshiTeich.Prologue.Arithmetic.localDeg w = ‖a‖ :=
    LocalCompletion.padicAlgClEquiv_norm_pow w a
  exact (congrArg (fun t : ℝ => t ^ JoshiTeich.Prologue.Arithmetic.localDeg w) hcoe).trans
    (hpow.trans (completionInAlgebraicClosure_norm w x))

end Completion

/-- The chosen Tate root mapped from its finite completion into standard `ℂ_p`. -/
noncomputable def qrootInPadicComplex (TL : ThetaLocalData D LT) (w : FinitePlace D.Kt) :
    PadicComplex (JoshiTeich.Prologue.Arithmetic.residueChar w) :=
  completionInPadicComplex w (TL.qroot w)

private theorem qrootInPadicComplex_norm_pow (TL : ThetaLocalData D LT) (w : FinitePlace D.Kt) :
    ‖TL.qrootInPadicComplex w‖ ^ Tripod.localDeg D.Kt w = ‖TL.qroot w‖ :=
  completionInPadicComplex_norm_pow w (TL.qroot w)

/-- In standard `ℂ_p` norms the representative product uses the normalized
arithmetic weight of the moduli place. -/
theorem sectionQRootProduct_eq_padicComplexProduct
    (TL : ThetaLocalData D LT) (QI : QPilotInputs D) (exponent : ℝ) :
    let M := ↥(fieldOfModuli D.F D.E)
    TL.sectionQRootProduct QI exponent =
      ∏ w ∈ QI.badModuliFinset,
        ‖TL.qrootInPadicComplex (D.localData.sect.sectFin w)‖ ^ (exponent * placeWeight M w) := by
  dsimp only
  let M := ↥(fieldOfModuli D.F D.E)
  let _ : Algebra M D.Kt := D.algebraModK
  rw [sectionQRootProduct]
  refine Finset.prod_congr rfl fun w _ => ?_
  let s := D.localData.sect.sectFin w
  have hsw : FinitePlace.LiesOver s w := D.localData.sect.sectFin_liesOver w
  have hdegree : Tripod.localDeg D.Kt s = Tripod.localDeg M w * Tripod.relLocalDeg s w :=
    Tripod.localDeg_eq_mul hsw
  have hrel : (Tripod.relLocalDeg s w : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Tripod.relLocalDeg_ne_zero hsw)
  rw [← qrootInPadicComplex_norm_pow TL s,
    ← Real.rpow_natCast_mul (norm_nonneg (TL.qrootInPadicComplex s))]
  apply congrArg (fun a : ℝ => ‖TL.qrootInPadicComplex s‖ ^ a)
  change (Tripod.localDeg D.Kt s : ℝ) *
      (exponent / ((Tripod.relLocalDeg s w : ℝ) * (Module.finrank ℚ M : ℝ))) =
    exponent * ((Tripod.localDeg M w : ℝ) / (Module.finrank ℚ M : ℝ))
  rw [← mul_div_assoc, hdegree, Nat.cast_mul, mul_right_comm,
    mul_comm (Tripod.relLocalDeg s w : ℝ) (Module.finrank ℚ M : ℝ),
    mul_div_mul_right _ _ hrel, mul_comm (Tripod.localDeg M w : ℝ) exponent, mul_div_assoc]

/-- The weighted standard-norm product with the square exponents based at
label `m`, expressed in the finite packet volumes. -/
theorem log_normalized_sectionPadicComplexProduct_eq_sum_finite_packetVol
    (hModuli : @algebraMap ↥(fieldOfModuli D.F D.E) D.Kt _ _ D.algebraModK =
      (algebraMap D.F D.Kt).comp (algebraMap ↥(fieldOfModuli D.F D.E) D.F))
    (TL : ThetaLocalData D (LocalConstruct.concreteLocalTheory (K := D.Kt)))
    (QI : QPilotInputs D) :
    let m := (D.ℓ - 1) / 2
    let M := ↥(fieldOfModuli D.F D.E)
    let R := TL.rhsData
    Real.log (∏ i : Fin m, ∏ w ∈ QI.badModuliFinset,
      ‖TL.qrootInPadicComplex (D.localData.sect.sectFin w)‖ ^
        ((((i.1 + 1 : ℕ) : ℝ) / (m : ℝ)) ^ 2 * placeWeight M w)) =
      (∑ i : Fin m, ∑ p ∈ TL.badChars.attach,
        let q := RationalPlace.finite ⟨p.1, TL.badChars_prime p.1 p.2⟩
        R.vol.packetVol i q ((R.thetaHull i).region q)) / (m : ℝ) ^ 2 := by
  simpa only [sectionQRootProduct_eq_padicComplexProduct] using
    log_normalized_sectionQRootProduct_eq_sum_finite_packetVol hModuli TL QI

end AbcAdaptation.Reference.Iut.ThetaLocalData
