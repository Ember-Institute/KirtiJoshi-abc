import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
`refer/iut/Iut/Anabelian/Genuine/Homs.lean`, valuation of a normalization prime;
Mathlib HeightOneSpectrum.valuation and valuation equivalence.
fidelity: the actual valuation subring at a nonzero Dedekind prime contains the
coordinate ring. Prime membership is equivalent to valuation less than one.
boundary: Scene1/Derived. This is a local algebra comparison, not a covering law.
-/

namespace JoshiTeich.Act1Scene1.NormalizationPrimeValuation

open IsDedekindDomain
noncomputable section
variable {R K : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The valuation subring at the given height-one prime. -/
def primeSubring (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : HeightOneSpectrum R) : ValuationSubring K :=
  (p.valuation K).valuationSubring

theorem coordinate_mem (p : HeightOneSpectrum R) (a : R) :
    algebraMap R K a ∈ primeSubring K p := p.valuation_le_one a

theorem valuation_lt_one_iff_mem (p : HeightOneSpectrum R) (a : R) :
    (primeSubring K p).valuation (algebraMap R K a) < 1 ↔ a ∈ p.asIdeal :=
  (Valuation.isEquiv_valuation_valuationSubring (p.valuation K)).lt_one_iff_lt_one.symm.trans
    (p.valuation_lt_one_iff_mem a)

end
end JoshiTeich.Act1Scene1.NormalizationPrimeValuation
