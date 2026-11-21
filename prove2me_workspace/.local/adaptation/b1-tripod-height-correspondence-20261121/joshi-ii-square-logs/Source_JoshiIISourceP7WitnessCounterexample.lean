import Solutions.Source_JoshiIIP7NormalizedWitness
import Solutions.Source_ReferenceIutPointModuliMap
import Solutions.Source_TripodRationalLegendreFiveP7Counterexample

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open Reference.Iut

variable {AG : AnabelianGeometry.{0}} {TG : TemperedGeometry AG}

/-- On the actual P7 data, the normalized witness average uses the same chosen
point, prime, local theory, root family, and q-pilot inputs. -/
theorem exists_normalizedWitnessLogAverage_of_sourceP7 {K : CompactlyBounded} {d : ℕ}
    (CI : CurveInputs tripodTheory AG K d) (anab : AnabelianExistence AG TG)
    {X : Corollary312VariantData.{0, 0} AG TG} (hX : IsSourceP7Variant CI anab X) :
    ∃ (D : InitialThetaData AG TG) (LT : LocalTheory.{0, 0} D.Kt)
      (TL : ThetaLocalData D LT) (QI : QPilotInputs D),
      X = concreteVariantData D LT TL QI ∧ X.qPilot.lhs < TL.normalizedWitnessLogAverage QI := by
  rcases hX with ⟨x, hx, hxe, ℓ, hprime, h7, hP2, _, hP5, hsl, htwo, hEq⟩
  let P := CI.pointThetaData anab x hx hxe ℓ hprime h7 hP2 hP5 hsl
  let TL := (P.localThetaData htwo).withBadChars P.qPilotInputs
  refine ⟨P.data, P.localTheory, TL, P.qPilotInputs, hEq, ?_⟩
  rw [hEq]
  exact TL.qPilot_lhs_lt_normalizedWitnessLogAverage P.qPilotInputs
    (CI.pointThetaData_algebraMap_moduli_torsion anab x hx hxe ℓ hprime h7 hP2 hP5 hsl)

/-- The degree-one Legendre counterexample has hull volume strictly below the
normalized numerical witness from the same P7 data. -/
theorem exists_sourceP7Hull_lt_normalizedWitnessLogAverage_rationalLegendreFiveLocus
    (P : CurveProviders) (hcore : CoreFinitenessHyp P rationalLegendreFiveLocus 1 AG)
    (anab : AnabelianExistence AG TG) :
    let K := rationalLegendreFiveLocus
    let CF : CurveFactsProp P K 1
        (cyclicConst K (torsionConst K.c (legendre_torsion_x_le K.c))) := ⟨cyclicBoundOdd P K 1⟩
    let CI := curveInputs_from_source P K 1 CF hcore northcottHyp
      (legendreHeight P K) (twoAdicBound P K)
    ∃ (D : InitialThetaData AG TG) (LT : LocalTheory.{0, 0} D.Kt)
      (TL : ThetaLocalData D LT) (QI : QPilotInputs D),
      let X := concreteVariantData D LT TL QI
      IsSourceP7Variant CI anab X ∧ X.rhsData.rhs < TL.normalizedWitnessLogAverage QI := by
  intro K CF CI
  obtain ⟨X, hX, hRhs⟩ := exists_sourceP7Counterexample_rationalLegendreFiveLocus P hcore anab
  obtain ⟨D, LT, TL, QI, rfl, hQ⟩ := exists_normalizedWitnessLogAverage_of_sourceP7 CI anab hX
  exact ⟨D, LT, TL, QI, hX, hRhs.trans hQ⟩

end AbcAdaptation.Tripod

#print axioms AbcAdaptation.Tripod.exists_normalizedWitnessLogAverage_of_sourceP7
#print axioms AbcAdaptation.Tripod.exists_sourceP7Hull_lt_normalizedWitnessLogAverage_rationalLegendreFiveLocus
