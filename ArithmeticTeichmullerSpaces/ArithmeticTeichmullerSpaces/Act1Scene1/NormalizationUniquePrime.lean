import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Ideal.GoingUp

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`.
fidelity: an integral intermediate ring in the same fraction field has a unique prime above an integrally closed localization.
Original proofs; no reference implementation copied.
boundary: this does not identify the infinity fiber with a projective cusp,
`AG.Cusp`, the distinguished torsion class or the theta-root model.
-/

namespace JoshiTeich.Act1Scene1.NormalizationUniquePrime

noncomputable section

variable {R A : Type*} [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]

/-- The elementary denominator criterion for uniqueness above a prime. -/
theorem primesOver_subsingleton_of_denominators
    (p : Ideal R) [p.IsPrime]
    (hden : ∀ x : A, ∃ a : R, ∃ s : p.primeCompl,
      x * algebraMap R A s = algebraMap R A a) :
    Subsingleton (p.primesOver A) := by
  refine ⟨fun q q' => Subtype.ext ?_⟩
  apply Ideal.ext
  intro x
  obtain ⟨a, s, hs⟩ := hden x
  have hmem (Q : p.primesOver A) : x ∈ Q.1 ↔ a ∈ p := by
    have hsnot : algebraMap R A s ∉ Q.1 := by
      intro hsQ
      exact s.2 ((Q.1.mem_of_liesOver p (s : R)).mpr hsQ)
    rw [Q.1.mem_of_liesOver p a, ← hs]
    exact (Ideal.IsPrime.mul_mem_right_iff hsnot).symm
  exact (hmem q).trans (hmem q').symm

/-- Integrality plus normality at p clears denominators outside p. -/
theorem denominators_of_isIntegrallyClosed_atPrime
    [Algebra.IsIntegral R A]
    (p : Ideal R) [p.IsPrime] [IsIntegrallyClosed (Localization.AtPrime p)]
    (g : A →ₐ[R] FractionRing R) (hg : Function.Injective g) (x : A) :
    ∃ a : R, ∃ s : p.primeCompl,
      x * algebraMap R A s = algebraMap R A a := by
  let L := Localization.AtPrime p
  have hint : IsIntegral R (g x) := (Algebra.IsIntegral.isIntegral x).map g
  have hintL : IsIntegral L (g x) := hint.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hintL
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj p.primeCompl y
  refine ⟨a, s, hg ?_⟩
  have hF := congrArg (algebraMap L (FractionRing R)) hs
  simpa only [map_mul, hy,
    ← IsScalarTower.algebraMap_apply R L (FractionRing R), g.commutes] using hF

/-- Uniqueness for an integral subring of the same fraction field. -/
theorem primesOver_subsingleton_of_isIntegrallyClosed_atPrime
    [Algebra.IsIntegral R A]
    (p : Ideal R) [p.IsPrime] [IsIntegrallyClosed (Localization.AtPrime p)]
    (g : A →ₐ[R] FractionRing R) (hg : Function.Injective g) :
    Subsingleton (p.primesOver A) :=
  primesOver_subsingleton_of_denominators p
    (denominators_of_isIntegrallyClosed_atPrime p g hg)

/-- The arbitrary common fraction field interface. All hypotheses are structural:
the upper ring injects into K, K is Frac(R), and A is integral over R. -/
theorem primesOver_subsingleton_common_fractionField
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    [Algebra A K] [IsScalarTower R A K] [Algebra.IsIntegral R A]
    (p : Ideal R) [p.IsPrime] [IsIntegrallyClosed (Localization.AtPrime p)]
    (hinj : Function.Injective (algebraMap A K)) :
    Subsingleton (p.primesOver A) := by
  let e : FractionRing R ≃ₐ[R] K := FractionRing.algEquiv R K
  let g : A →ₐ[R] FractionRing R :=
    e.symm.toAlgHom.comp (IsScalarTower.toAlgHom R A K)
  apply primesOver_subsingleton_of_isIntegrallyClosed_atPrime p g
  exact e.symm.injective.comp hinj


end

end JoshiTeich.Act1Scene1.NormalizationUniquePrime
