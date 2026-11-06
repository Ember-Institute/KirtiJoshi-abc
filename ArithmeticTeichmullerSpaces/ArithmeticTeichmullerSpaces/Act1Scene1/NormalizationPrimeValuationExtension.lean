import ArithmeticTeichmullerSpaces.Act1Scene1.NormalizationPrimeValuation
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
source-id: JT-SCENE1-NORMALIZATION-PRIME-AMBIENT-VALUATION-20261107
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
Mathlib `IsLocalRing.exists_factor_valuationRing` and the valuation ring of a
nonzero Dedekind prime.
fidelity: extends the actual prime valuation ring to the ambient field. Every
coordinate-ring element lies in the extension, and its valuation is less than
one exactly when it belongs to the original prime.
Original proofs; no reference implementation copied.
boundary: a valuation-center realization, without a torsion-cusp, distinguished
cusp, theta-root, or arbitrary orbicurve identification.
-/

namespace JoshiTeich.Act1Scene1.NormalizationPrimeValuation

open IsDedekindDomain
noncomputable section

variable {R K Ω : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω]

/-- An ambient valuation ring with precisely the original prime as its center. -/
theorem exists_ambient_valuation (f : K →+* Ω) (p : HeightOneSpectrum R) :
    ∃ W : ValuationSubring Ω,
      (∀ a : R, f (algebraMap R K a) ∈ W) ∧
      (∀ a : R, W.valuation (f (algebraMap R K a)) < 1 ↔ a ∈ p.asIdeal) := by
  let V := primeSubring K p
  let g : V →+* Ω := f.comp V.subtype
  obtain ⟨W, hW, hlocal⟩ := IsLocalRing.exists_factor_valuationRing g
  let j : V →+* W := g.codRestrict W.toSubring hW
  have : IsLocalHom j := hlocal
  refine ⟨W, ?_, ?_⟩
  · intro a
    exact hW ⟨algebraMap R K a, coordinate_mem p a⟩
  · intro a
    let aV : V := ⟨algebraMap R K a, coordinate_mem p a⟩
    change W.valuation (j aV) < 1 ↔ a ∈ p.asIdeal
    rw [← W.valuation_lt_one_iff (j aV)]
    change aV ∈ (IsLocalRing.maximalIdeal W).comap j ↔ a ∈ p.asIdeal
    rw [IsLocalRing.maximalIdeal_comap j, V.valuation_lt_one_iff aV]
    exact valuation_lt_one_iff_mem p a

end
end JoshiTeich.Act1Scene1.NormalizationPrimeValuation
