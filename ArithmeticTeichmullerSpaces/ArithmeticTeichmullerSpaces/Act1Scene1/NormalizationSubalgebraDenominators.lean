import ArithmeticTeichmullerSpaces.Act1Scene1.NormalizationCommonFractionResidue
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: the existing normalization denominator theorem and canonical subalgebra tower.
fidelity: factors structural conversion before actual specialization; no new assumption.
boundary: the actual consumer supplies the same raw chart and normalization ring.
-/

namespace JoshiTeich.Act1Scene1.NormalizationResidueConstants

noncomputable section

/-- Clear denominators through the canonical tower of an actual subalgebra. -/
theorem denominators_subalgebra_common_fractionField
    {k A K : Type*} [CommRing k] [CommRing A] [IsDomain A]
    [Field K] [Algebra k A] [Algebra A K]
    (B : Subalgebra k A) (p : Ideal B) [p.IsPrime]
    (hfrac : IsFractionRing B K)
    (hint : Algebra.IsIntegral B A)
    (hclosed : IsIntegrallyClosed (Localization.AtPrime p))
    (hinj : Function.Injective (algebraMap A K)) (x : A) :
    ∃ a : B, ∃ s : p.primeCompl,
      x * algebraMap B A s = algebraMap B A a := by
  haveI : IsFractionRing B K := hfrac
  haveI : Algebra.IsIntegral B A := hint
  haveI : IsIntegrallyClosed (Localization.AtPrime p) := hclosed
  haveI : IsScalarTower B A K :=
    IsScalarTower.of_algebraMap_eq (R := B) (S := A) (A := K) (fun _ => rfl)
  exact denominators_common_fractionField (R := B) (A := A) (K := K) p hinj x

end
end JoshiTeich.Act1Scene1.NormalizationResidueConstants
