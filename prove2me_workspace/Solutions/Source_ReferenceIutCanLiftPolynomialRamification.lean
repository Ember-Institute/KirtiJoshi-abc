/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/U2/Assembly.lean, `comap_aeval_span` and `ramificationIdx_aeval`
-/
import Solutions.Source_ReferenceIutCanLiftPolynomialDegree
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.RingTheory.RamificationInertia.Ramification

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open Polynomial

variable {k : Type*} [Field k]

/-- The closed point of the affine line with coordinate `w`. -/
noncomputable def polynomialPointIdeal (w : k) : Ideal k[X] := Ideal.span {X - C w}

theorem polynomialPointIdeal_isMaximal (w : k) : (polynomialPointIdeal w).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C w)

theorem polynomialPointIdeal_comap_aeval (p : k[X]) (w : k) :
    (polynomialPointIdeal w).comap (aeval (R := k) p).toRingHom =
      polynomialPointIdeal (p.eval w) := by
  ext q
  simp only [polynomialPointIdeal, Ideal.mem_comap, Ideal.mem_span_singleton, dvd_iff_isRoot,
    IsRoot.def]
  change eval w (aeval p q) = 0 ↔ eval (p.eval w) q = 0
  rw [← comp_eq_aeval, eval_comp]

/-- The local ramification index of an injective polynomial map at `w` is the multiplicity
of `w` in `p - p(w)`. -/
theorem ramificationIdx_aeval_eq_polynomialRamificationIdx {p : k[X]}
    (hinj : Function.Injective (aeval (R := k) p)) (w : k) :
    (letI := (aeval (R := k) p).toRingHom.toAlgebra;
      (polynomialPointIdeal w).ramificationIdx k[X]) = polynomialRamificationIdx p w := by
  letI := (aeval (R := k) p).toRingHom.toAlgebra
  let v := polynomialPointIdeal (p.eval w)
  let q := polynomialPointIdeal w
  letI : q.IsPrime := (polynomialPointIdeal_isMaximal w).isPrime
  letI : q.LiesOver v := ⟨(polynomialPointIdeal_comap_aeval p w).symm⟩
  have hmap : v.map (algebraMap k[X] k[X]) = Ideal.span {p - C (p.eval w)} := by
    change (Ideal.span {X - C (p.eval w)}).map (algebraMap k[X] k[X]) = _
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    change aeval (R := k) p (X - C (p.eval w)) = _
    simp
  have hne : p - C (p.eval w) ≠ 0 := by
    intro h
    apply X_sub_C_ne_zero (p.eval w)
    apply hinj
    simpa only [map_sub, aeval_X, aeval_C, algebraMap_eq, map_zero] using h
  have hvmap : v.map (algebraMap k[X] k[X]) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]
    exact hne
  change q.ramificationIdx k[X] = _
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx' v q hvmap]
  unfold polynomialRamificationIdx
  apply Ideal.ramificationIdx'_spec
  · change v.map (algebraMap k[X] k[X]) ≤ (Ideal.span {X - C w}) ^ _
    rw [hmap, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
    exact pow_rootMultiplicity_dvd _ _
  · change ¬ v.map (algebraMap k[X] k[X]) ≤ (Ideal.span {X - C w}) ^ _
    rw [hmap, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
    exact pow_rootMultiplicity_not_dvd hne _

end AbcAdaptation.Reference.Iut.Anabelian
