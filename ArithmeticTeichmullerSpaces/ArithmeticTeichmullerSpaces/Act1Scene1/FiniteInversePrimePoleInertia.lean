import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationGalois
import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationZeroFiber
import ArithmeticTeichmullerSpaces.Act1Scene1.NormalizationPrimeValuationInertia
import ArithmeticTeichmullerSpaces.Act1Scene1.PoleDivisionPointInertia

/-!
Original composition of existing project theorems.
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III ss:theta-data-fixing2;
the actual normalization valuation and the original pole-division inertia proof.
boundary: finite inverse-chart prime inertia only. The source point and all
field membership hypotheses must be discharged from the same actual seed.
-/

namespace JoshiTeich.Act1Scene1.FiniteInversePrimePoleInertia

open WeierstrassCurve IsDedekindDomain FunctionFieldNormalization
open scoped Classical IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section
attribute [local instance 2000] Classical.propDecidable

variable {k Ω : Type u} [Field k] [CharZero k] [Field Ω] [Algebra k Ω]
variable (t : Ω) (ht : Transcendental k t)
variable (N : IntermediateField (rationalBase k t) Ω)
  [FiniteDimensional (rationalBase k t) N] [IsGalois (rationalBase k t) N]

local instance : IsFractionRing (coordRing t N) N := fractionFieldRing t N
attribute [local instance] galoisNormalizationCoeffComm fieldRingAction

/-- A zero of the inverse coordinate is a pole in the finite prime valuation. -/
theorem not_mem_primeSubring_of_inverse_center
    (p : HeightOneSpectrum (coordRing t N)) (xg : N) (hxg : xg ≠ 0)
    (hinv : algebraMap (coordRing t N) N
      (algebraMap (polynomialBase k t) (coordRing t N) (polynomialCoordinate t)) = xg⁻¹)
    (hp : algebraMap (polynomialBase k t) (coordRing t N)
      (polynomialCoordinate t) ∈ p.asIdeal) :
    letI := dedekindRing t ht N
    xg ∉ NormalizationPrimeValuation.primeSubring N p := by
  letI := dedekindRing t ht N
  let W := NormalizationPrimeValuation.primeSubring N p
  have hsmall : W.valuation (xg⁻¹) < 1 := by
    rw [← hinv]
    exact (NormalizationPrimeValuation.valuation_lt_one_iff_mem p _).mpr hp
  have hnonunit := W.mem_nonunits_iff.mpr hsmall
  exact (W.inv_mem_nonunits_iff.mp hnonunit).resolve_left hxg

include ht

/-- Actual finite prime inertia supplies the whole-local-ring condition itself. -/
theorem inertia_fixes_of_inverse_center
    (E : WeierstrassCurve k) [E.IsElliptic]
    (p : HeightOneSpectrum (coordRing t N))
    (τ : N ≃ₐ[rationalBase k t] N)
    (hτ : τ ∈ p.asIdeal.inertia (N ≃ₐ[rationalBase k t] N))
    (n : ℕ) (hn : 0 < n) (hodd : Odd n)
    (R : E.toAffine.Point) (hR : R ≠ 0) (hTwo : 2 • R = 0)
    {xg yg : N} (hxg : xg ≠ 0)
    (hG : (E⁄N).toAffine.Nonsingular xg yg)
    (hinv : algebraMap (coordRing t N) N
      (algebraMap (polynomialBase k t) (coordRing t N) (polynomialCoordinate t)) = xg⁻¹)
    (hp : algebraMap (polynomialBase k t) (coordRing t N)
      (polynomialCoordinate t) ∈ p.asIdeal)
    (hτG : Affine.Point.map (W' := E) (S := k) (τ.toAlgHom.restrictScalars k)
      (Affine.Point.some xg yg hG) = Affine.Point.some xg yg hG)
    (Q : (E⁄N).toAffine.Point) (hQ : n • Q = Affine.Point.some xg yg hG) :
    Affine.Point.map (W' := E) (S := k) (τ.toAlgHom.restrictScalars k) Q = Q := by
  letI := dedekindRing t ht N
  let W := NormalizationPrimeValuation.primeSubring N p
  have hk (c : k) : algebraMap k N c ∈ W := by
    exact NormalizationPrimeValuation.coordinate_mem p
      (algebraMap k (coordRing t N) c)
  have hi : ∀ a ∈ W, W.valuation (τ a - a) < 1 := by
    intro a ha
    exact NormalizationPrimeValuation.inertia_lt_one_of_mem_primeSubring
      p τ τ.toRingEquiv (fun _ => rfl) hτ a ha
  exact PoleDivisionPointInertia.inertia_fixes_of_nsmul_pole E W hk
    (τ.toAlgHom.restrictScalars k) hi n hn hodd R hR hTwo hG
    (not_mem_primeSubring_of_inverse_center t ht N p xg hxg hinv hp) hτG Q hQ

end
end JoshiTeich.Act1Scene1.FiniteInversePrimePoleInertia
