import ArithmeticTeichmullerSpaces.Prologue.Audit.Checks
import ArithmeticTeichmullerSpaces.Prologue.Audit.ImportAudit
import ArithmeticTeichmullerSpaces.Act1Scene1
import ArithmeticTeichmullerSpaces.Prologue.Audit.AxiomAudit
import Solutions.Source_ReferenceIutCor312FiniteThetaHullVolume
import Solutions.Source_ReferenceIutCor312RepresentativeQPilot
import Solutions.Source_ReferenceIutPointModuliMap
import Solutions.Source_TripodP7
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.ThetaLocalData

open NumberField
open scoped BigOperators

universe u v

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {D : InitialThetaData AG TG} {LT : LocalTheory.{u, v} D.Kt}

/-- The weighted product of the chosen Tate-root norms at the section places.
The exponent at each bad moduli place is divided by its relative local degree
and the absolute degree of the moduli field. -/
noncomputable def sectionQRootProduct (TL : ThetaLocalData D LT) (QI : QPilotInputs D)
    (exponent : ℝ) : ℝ :=
  let M := ↥(fieldOfModuli D.F D.E)
  letI : Algebra M D.Kt := D.algebraModK
  ∏ w ∈ QI.badModuliFinset,
    ‖TL.qroot (D.localData.sect.sectFin w)‖ ^
      (exponent / ((Tripod.relLocalDeg (D.localData.sect.sectFin w) w : ℝ) *
        (Module.finrank ℚ M : ℝ)))

private theorem sectionQRootProduct_pos (TL : ThetaLocalData D LT) (QI : QPilotInputs D)
    (exponent : ℝ) : 0 < TL.sectionQRootProduct QI exponent := by
  unfold sectionQRootProduct
  exact Finset.prod_pos fun w _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (TL.qroot_ne_zero (D.localData.sect.sectFin w))) _

section ModuliMap

variable (hModuli :
  @algebraMap ↥(fieldOfModuli D.F D.E) D.Kt _ _ D.algebraModK =
    (algebraMap D.F D.Kt).comp (algebraMap ↥(fieldOfModuli D.F D.E) D.F))

include hModuli

/-- The weighted product has logarithm equal to the signed q-pilot times the exponent. -/
theorem log_sectionQRootProduct (TL : ThetaLocalData D LT) (QI : QPilotInputs D)
    (exponent : ℝ) :
    Real.log (TL.sectionQRootProduct QI exponent) =
      exponent * (concreteVariantData D LT TL QI).qPilot.lhs := by
  have hpos (w : FinitePlace ↥(fieldOfModuli D.F D.E)) :
      0 < ‖TL.qroot (D.localData.sect.sectFin w)‖ :=
    norm_pos_iff.mpr (TL.qroot_ne_zero _)
  rw [sectionQRootProduct, TL.qPilot_lhs_eq_sum_section_log_norm QI hModuli,
    ← mul_div_assoc, Finset.mul_sum, Finset.sum_div]
  rw [Real.log_prod (fun w _ => (Real.rpow_pos_of_pos (hpos w) _).ne')]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Real.log_rpow (hpos w), div_mul_eq_mul_div, ← mul_div_assoc, div_div]

/-- The finite packet volumes for a capsule sum to the log of the weighted
representative product with that capsule's distinguished label squared. -/
theorem sum_finite_packetVol_eq_log_sectionQRootProduct
    (TL : ThetaLocalData D (LocalConstruct.concreteLocalTheory (K := D.Kt)))
    (QI : QPilotInputs D) (i : Fin ((D.ℓ - 1) / 2)) :
    let R := TL.rhsData
    (∑ p ∈ TL.badChars.attach,
      let q := RationalPlace.finite ⟨p.1, TL.badChars_prime p.1 p.2⟩
      R.vol.packetVol i q ((R.thetaHull i).region q)) =
      Real.log (TL.sectionQRootProduct QI (((i.1 + 1 : ℕ) : ℝ) ^ 2)) := by
  let X := concreteVariantData D _ TL QI
  let square : ℝ := ((i.1 + 1 : ℕ) : ℝ) ^ 2
  have hlogQ : ∑ p ∈ TL.badChars, X.logQAt p = X.qPilot.logQ := by
    unfold Corollary312VariantData.logQAt QPilotData.logQ
    exact Finset.sum_fiberwise_of_maps_to
      (fun w _ => TL.bad_residueChar_mem w.1 (X.qPilot.mem_bad w.2)) _
  rw [log_sectionQRootProduct hModuli]
  calc
    _ = ∑ p ∈ TL.badChars.attach, square * -(X.logQAt p.1 / (2 * (D.ℓ : ℝ))) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [mul_neg, ← neg_mul]
      exact TL.packetVol_finite_thetaHull QI i ⟨p.1, TL.badChars_prime p.1 p.2⟩
    _ = square * X.qPilot.lhs := by
      rw [← Finset.mul_sum, Finset.sum_neg_distrib, ← Finset.sum_div,
        Finset.sum_attach TL.badChars X.logQAt, hlogQ]
      rfl

/-- The weighted root-norm product with the normalized square exponents of
Joshi III, (9.9.4)–(9.9.6), expressed in the finite packet volumes. -/
theorem log_normalized_sectionQRootProduct_eq_sum_finite_packetVol
    (TL : ThetaLocalData D (LocalConstruct.concreteLocalTheory (K := D.Kt)))
    (QI : QPilotInputs D) :
    let m := (D.ℓ - 1) / 2
    let R := TL.rhsData
    Real.log (∏ i : Fin m, TL.sectionQRootProduct QI
      ((((i.1 + 1 : ℕ) : ℝ) / (m : ℝ)) ^ 2)) =
      (∑ i : Fin m, ∑ p ∈ TL.badChars.attach,
        let q := RationalPlace.finite ⟨p.1, TL.badChars_prime p.1 p.2⟩
        R.vol.packetVol i q ((R.thetaHull i).region q)) / (m : ℝ) ^ 2 := by
  dsimp only
  rw [Real.log_prod (fun _ _ => (sectionQRootProduct_pos TL QI _).ne'), Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [log_sectionQRootProduct hModuli,
    sum_finite_packetVol_eq_log_sectionQRootProduct hModuli TL QI i,
    log_sectionQRootProduct hModuli, div_pow, mul_div_right_comm]

end ModuliMap

end AbcAdaptation.Reference.Iut.ThetaLocalData

namespace AbcAdaptation.Tripod

open Reference.Iut
open scoped BigOperators

variable {AG : AnabelianGeometry.{0}} {TG : TemperedGeometry AG}

/-- Apply the finite volume identity to the bundle recorded by the source P7 predicate. -/
theorem sourceP7_normalized_sectionQRootProduct_eq_finite_packetVol
    {K : CompactlyBounded} {d : ℕ}
    (CI : CurveInputs tripodTheory AG K d) (anab : AnabelianExistence AG TG)
    {X : Corollary312VariantData.{0, 0} AG TG} (hX : IsSourceP7Variant CI anab X) :
    ∃ (D : InitialThetaData AG TG)
      (TL : ThetaLocalData D (LocalConstruct.concreteLocalTheory (K := D.Kt))) (QI : QPilotInputs D),
      X = concreteVariantData D _ TL QI ∧
      (let m := (D.ℓ - 1) / 2
       let R := TL.rhsData
       Real.log (∏ i : Fin m, TL.sectionQRootProduct QI
         ((((i.1 + 1 : ℕ) : ℝ) / (m : ℝ)) ^ 2)) =
         (∑ i : Fin m, ∑ p ∈ TL.badChars.attach,
           let q := RationalPlace.finite ⟨p.1, TL.badChars_prime p.1 p.2⟩
           R.vol.packetVol i q ((R.thetaHull i).region q)) / (m : ℝ) ^ 2) := by
  rcases hX with ⟨x, hx, hxe, ℓ, hprime, h7, hP2, _, hP5, hsl, htwo, hEq⟩
  let P := CI.pointThetaData anab x hx hxe ℓ hprime h7 hP2 hP5 hsl
  let TL := (P.localThetaData htwo).withBadChars P.qPilotInputs
  have hModuli := CI.pointThetaData_algebraMap_moduli_torsion anab x hx hxe ℓ hprime h7 hP2 hP5 hsl
  exact ⟨P.data, TL, P.qPilotInputs, hEq,
    ThetaLocalData.log_normalized_sectionQRootProduct_eq_sum_finite_packetVol
      hModuli TL P.qPilotInputs⟩

end AbcAdaptation.Tripod

#print axioms AbcAdaptation.Reference.Iut.ThetaLocalData.sectionQRootProduct
#print axioms AbcAdaptation.Reference.Iut.ThetaLocalData.log_sectionQRootProduct
#print axioms AbcAdaptation.Reference.Iut.ThetaLocalData.sum_finite_packetVol_eq_log_sectionQRootProduct
#print axioms AbcAdaptation.Reference.Iut.ThetaLocalData.log_normalized_sectionQRootProduct_eq_sum_finite_packetVol
#print axioms AbcAdaptation.Tripod.sourceP7_normalized_sectionQRootProduct_eq_finite_packetVol
