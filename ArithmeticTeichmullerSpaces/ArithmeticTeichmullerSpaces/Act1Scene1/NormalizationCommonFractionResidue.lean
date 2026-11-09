import ArithmeticTeichmullerSpaces.Act1Scene1.NormalizationResidueConstants

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: the already proved normalization denominator API and Mathlib's canonical
quotient-to-residue-field algebra map.
fidelity: factors only structural conversion; no new mathematical assumption.
boundary: the actual consumer must provide the original lower normalization.
-/

namespace JoshiTeich.Act1Scene1.NormalizationResidueConstants

open scoped Classical
noncomputable section

/-- Select the canonical coefficient algebra on a prime residue field before actual specialization. -/
@[instance_reducible] def residueCoefficientAlgebra
    {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (q : Ideal A) [q.IsPrime] : Algebra k q.ResidueField := inferInstance

/-- Express existing denominator clearing over an arbitrary common fraction field. -/
theorem denominators_common_fractionField
    {R A K : Type*} [CommRing R] [IsDomain R] [CommRing A]
    [Field K] [Algebra R A] [Algebra R K] [IsFractionRing R K]
    [Algebra A K] [IsScalarTower R A K] [Algebra.IsIntegral R A]
    (p : Ideal R) [p.IsPrime] [IsIntegrallyClosed (Localization.AtPrime p)]
    (hinj : Function.Injective (algebraMap A K)) (x : A) :
    ∃ a : R, ∃ s : p.primeCompl,
      x * algebraMap R A s = algebraMap R A a := by
  let e : FractionRing R ≃ₐ[R] K := FractionRing.algEquiv R K
  let g : A →ₐ[R] FractionRing R :=
    e.symm.toAlgHom.comp (IsScalarTower.toAlgHom R A K)
  exact NormalizationUniquePrime.denominators_of_isIntegrallyClosed_atPrime p g
    (e.symm.injective.comp hinj) x

/-- The canonical quotient-to-residue map transports coefficient surjectivity. -/
theorem residue_constants_surjective_of_quotient
    {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    (q : Ideal A) [q.IsMaximal]
    (hconst : Function.Surjective (algebraMap k (A ⧸ q))) :
    Function.Surjective (algebraMap k q.ResidueField) := by
  rw [IsScalarTower.algebraMap_eq k (A ⧸ q) q.ResidueField]
  exact q.bijective_algebraMap_quotient_residueField.surjective.comp hconst

end
end JoshiTeich.Act1Scene1.NormalizationResidueConstants
