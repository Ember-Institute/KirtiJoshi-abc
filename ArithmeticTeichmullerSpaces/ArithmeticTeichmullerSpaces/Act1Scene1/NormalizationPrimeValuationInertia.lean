import ArithmeticTeichmullerSpaces.Act1Scene1.NormalizationPrimeValuation
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.Algebra.Ring.Action.Group
import Mathlib.Tactic.Ring

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: the actual normalization-prime inertia and prime valuation;
Mathlib `HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer`,
`valuation_eq_one_iff_notMem`, and `Ideal.mem_inertia`.
fidelity: every element of the prime valuation ring is n/d with d outside
that prime. Coordinate inertia makes both numerator and denominator unchanged
modulo the prime, so it acts trivially on the residue of every element of
the entire valuation ring. No pointwise-inertia law is supplied as input.
boundary: Scene1/Derived. The compatibility argument identifies the existing
coordinate-ring action with the given field automorphism. This local algebra
result does not identify infinity points or assert an orbicurve realization.
-/

namespace JoshiTeich.Act1Scene1.NormalizationPrimeValuation

open IsDedekindDomain
noncomputable section

variable {R K G : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Group G] [MulSemiringAction G R]

/-- Prime inertia on the coordinate ring gives pointwise inertia on its entire local valuation ring. -/
theorem inertia_lt_one_of_mem_primeSubring
    (p : HeightOneSpectrum R) (g : G) (τ : K ≃+* K)
    (hcompat : ∀ a : R, τ (algebraMap R K a) = algebraMap R K (g • a))
    (hg : g ∈ p.asIdeal.inertia G)
    (x : K) (hx : x ∈ primeSubring K p) :
    (primeSubring K p).valuation (τ x - x) < 1 := by
  have hxval : p.valuation K x ≤ 1 := hx
  obtain ⟨n, d, hnd⟩ := p.exists_primeCompl_mul_eq_of_integer x hxval
  have hdiff (a : R) : g • a - a ∈ p.asIdeal := (Ideal.mem_inertia.mp hg) a
  have hd : (d : R) ∉ p.asIdeal := d.property
  have hgd : g • (d : R) ∉ p.asIdeal := by
    intro h
    apply hd
    have hm := p.asIdeal.sub_mem h (hdiff d)
    simpa only [sub_sub_cancel] using hm
  have hvd : p.valuation K (algebraMap R K (d : R)) = 1 :=
    p.valuation_eq_one_iff_notMem.mpr hd
  have hvgd : p.valuation K (algebraMap R K (g • (d : R))) = 1 :=
    p.valuation_eq_one_iff_notMem.mpr hgd
  have hτnd : τ x * algebraMap R K (g • (d : R)) = algebraMap R K (g • n) := by
    have h := congrArg τ hnd
    simpa only [map_mul, hcompat] using h
  let b : R := (g • n - n) * (d : R) - n * (g • (d : R) - d)
  have hb : b ∈ p.asIdeal :=
    p.asIdeal.sub_mem (p.asIdeal.mul_mem_right _ (hdiff n))
      (p.asIdeal.mul_mem_left _ (hdiff d))
  have hcross :
      (τ x - x) * (algebraMap R K (g • (d : R)) * algebraMap R K (d : R)) =
        algebraMap R K b := by
    calc
      _ = (τ x * algebraMap R K (g • (d : R))) * algebraMap R K (d : R) -
          (x * algebraMap R K (d : R)) * algebraMap R K (g • (d : R)) := by ring
      _ = algebraMap R K (g • n) * algebraMap R K (d : R) -
          algebraMap R K n * algebraMap R K (g • (d : R)) := by rw [hτnd, hnd]
      _ = algebraMap R K b := by
        simp only [b, map_sub, map_mul]
        ring
  have hsmall : p.valuation K (algebraMap R K b) < 1 :=
    (p.valuation_lt_one_iff_mem b).mpr hb
  rw [← hcross, map_mul, map_mul, hvgd, hvd, one_mul, mul_one] at hsmall
  exact (Valuation.isEquiv_valuation_valuationSubring (p.valuation K)).lt_one_iff_lt_one.mp hsmall

/-- The coordinate inertia subgroup satisfies the full valuation-ring pointwise condition. -/
theorem inertia_pointwise_primeSubring
    [MulSemiringAction G K]
    (p : HeightOneSpectrum R) (g : G)
    (hcompat : ∀ a : R, g • algebraMap R K a = algebraMap R K (g • a))
    (hg : g ∈ p.asIdeal.inertia G) :
    ∀ x ∈ primeSubring K p, (primeSubring K p).valuation (g • x - x) < 1 := by
  intro x hx
  exact inertia_lt_one_of_mem_primeSubring p g (MulSemiringAction.toRingEquiv G K g)
    hcompat hg x hx

end
end JoshiTeich.Act1Scene1.NormalizationPrimeValuation
