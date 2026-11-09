import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityFinitePrimeCoordinates
import ArithmeticTeichmullerSpaces.Act1Scene1.IntermediateFieldFixesAdjoin

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
the existing full division-coordinate adjoin identity and the same seed's
actual inverse-chart prime inertia.
fidelity: coordinate fixation closes under field generation, so the original
finite-prime inertia over the original lower field fixes the original unsigned
covering field. No ambient valuation lift is assumed.
boundary: the original infinity prime still needs a lying-over lift into this
finite closure. This file does not assert ramification index one, translation
inertia bottom, arithmetic prime-stabilizer freeness or a cusp identity.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve IsDedekindDomain
open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open FunctionFieldNormalization
open scoped Classical IntermediateField.algebraAdjoinAdjoin Pointwise
universe u
noncomputable section

attribute [local instance 2000] Classical.propDecidable
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] inverseCoordinateRationalBase_coefficientAlgebra
  inverseCoordinateRationalBase_coefficientSMul inverseCoordinateRationalBase_coefficientModule
  inverseCoordinatePolynomialBaseRationalBaseAlgebra inverseCoordinatePolynomialBaseRationalBaseSMul
  inverseCoordinatePolynomialBaseRationalBaseModule inverseCoordinatePolynomialBaseRationalBaseTower
  infinityDivisionNormalClosure_field infinityDivisionNormalClosure_rationalAlgebra
  infinityDivisionNormalClosure_baseAlgebra infinityDivisionNormalClosure_baseSMul
  infinityDivisionNormalClosure_baseModule infinityDivisionNormalClosure_coefficientAlgebra
  infinityDivisionNormalClosure_coefficientSMul infinityDivisionNormalClosure_coefficientModule
  infinityDivisionNormalClosure_coefficientBaseTower infinityDivisionNormalClosure_baseTower
  infinityDivisionClosure_separable infinityDivisionClosureRing_baseAlgebra
  infinityDivisionClosureRing_dedekind infinityDivisionClosureRing_fraction
  galoisNormalizationCoeffComm fieldRingAction

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

variable
    (p : HeightOneSpectrum
      (coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityDivisionNormalClosure))
    (hp : algebraMap
      (polynomialBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
      (coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityDivisionNormalClosure)
      (polynomialCoordinate (Genuine.xG S.prime.EK)⁻¹) ∈ p.asIdeal)

include hp

/-- Actual inverse-prime inertia over the lower field fixes the whole full division field. -/
theorem infinityClosurePrime_inertia_fixes_fullDivision
    (τ : S.infinityDivisionNormalClosure ≃ₐ[
      rationalBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹]
      S.infinityDivisionNormalClosure)
    (hτ : τ ∈ p.asIdeal.inertia
      (S.infinityDivisionNormalClosure ≃ₐ[
        rationalBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹]
        S.infinityDivisionNormalClosure))
    (hF : τ ∈ fixSub S.infinityDivisionNormalClosure S.infinityTranslationBaseField)
    (a : S.infinityDivisionNormalClosure)
    (ha : (a : Genuine.Ω S.prime.EK) ∈
      Genuine.normalizationField S.prime.EK S.prime.ℓ ⊥ false) : τ a = a := by
  have hc := S.infinityClosurePrime_inertia_fixes_coordinates p hp τ hτ hF
  rw [Genuine.normalizationFullDivision_eq_adjoin] at ha
  refine fixes_rebased_adjoin S.infinityTranslation_xLine_eq_inverseCoordinateLine
    S.infinityDivisionNormalClosure τ
    {ptX (Genuine.Qpt S.prime.EK S.prime.ℓ),
      ptY (Genuine.Qpt S.prime.EK S.prime.ℓ)} ?_ a ha
  rintro b (rfl | rfl)
  · exact ⟨S.infinityDivisionNormalClosure_Qpt_coordinates_mem.1, hc.1⟩
  · exact ⟨S.infinityDivisionNormalClosure_Qpt_coordinates_mem.2, hc.2⟩

/-- The same finite inertia fixes the original unsigned cover field in the original infinity chart. -/
theorem infinityClosurePrime_inertia_fixes_unsignedField
    (τ : S.infinityDivisionNormalClosure ≃ₐ[
      rationalBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹]
      S.infinityDivisionNormalClosure)
    (hτ : τ ∈ p.asIdeal.inertia
      (S.infinityDivisionNormalClosure ≃ₐ[
        rationalBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹]
        S.infinityDivisionNormalClosure))
    (hF : τ ∈ fixSub S.infinityDivisionNormalClosure S.infinityTranslationBaseField)
    (a : S.infinityDivisionNormalClosure)
    (ha : (a : Genuine.Ω S.prime.EK) ∈ S.infinityNormalizationField false) : τ a = a := by
  have hu := (S.mem_infinityNormalizationField false (a : Genuine.Ω S.prime.EK)).mp ha
  exact S.infinityClosurePrime_inertia_fixes_fullDivision p hp τ hτ hF a
    (Genuine.normalizationField_le_fullDivision
      S.prime.EK S.prime.ℓ S.prime.M false hu)

/-- The exact finite inertia containment needed by the ramification criterion. -/
theorem infinityClosurePrime_inertia_fixSub_le :
    p.asIdeal.inertia
        (S.infinityDivisionNormalClosure ≃ₐ[
          rationalBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹]
          S.infinityDivisionNormalClosure) ⊓
      fixSub S.infinityDivisionNormalClosure S.infinityTranslationBaseField ≤
    fixSub S.infinityDivisionNormalClosure (S.infinityNormalizationField false) := by
  intro τ hτ
  exact mem_fixSub.mpr fun a ha =>
    S.infinityClosurePrime_inertia_fixes_unsignedField p hp τ hτ.1 hτ.2 a ha

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
