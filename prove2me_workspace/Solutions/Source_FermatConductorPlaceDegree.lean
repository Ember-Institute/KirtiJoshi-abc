/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Independent source adaptation. Pinned proofs and consumer mappings: SOURCE_LEDGER.md.
-/
import Definitions.Def_FermatBelyiConductorExtensionFinitePlaces

set_option autoImplicit false
open NumberField IsDedekindDomain Module

namespace AbcAdaptation.Tripod.Fermat.Proper.ConductorExtensionSource

variable {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]

/-- `log N(w) = f·log N(u)` for `w` over `u`. -/
lemma log_placeNorm_eq {w : FinitePlace L} {u : FinitePlace F} (h : PlaceLiesOver w u) :
    Real.log (placeNorm w) = placeInertiaDeg w u * Real.log (placeNorm u) := by
  rw [placeNorm_eq_pow h, Nat.cast_pow, Real.log_pow]

/-- The finite place of `L` of a prime of `𝓞 L` over `𝔭_u`. -/
noncomputable def placeOfPrimeOver (u : FinitePlace F) {P : Ideal (𝓞 L)}
    (hP : P ∈ IsDedekindDomain.primesOverFinset u.maximalIdeal.asIdeal (𝓞 L)) : FinitePlace L :=
  haveI := u.maximalIdeal.isMaximal
  FinitePlace.mk
    ⟨P, ((mem_primesOverFinset_iff' u.maximalIdeal.ne_bot).mp hP).1, by
      obtain ⟨_, _⟩ := (mem_primesOverFinset_iff' u.maximalIdeal.ne_bot).mp hP
      exact Ideal.ne_bot_of_liesOver_of_ne_bot u.maximalIdeal.ne_bot P⟩

lemma placeOfPrimeOver_maximalIdeal (u : FinitePlace F) {P : Ideal (𝓞 L)}
    (hP : P ∈ IsDedekindDomain.primesOverFinset u.maximalIdeal.asIdeal (𝓞 L)) :
    (placeOfPrimeOver u hP).maximalIdeal.asIdeal = P := by
  rw [placeOfPrimeOver, FinitePlace.maximalIdeal_mk]

lemma placeLiesOver_placeOfPrimeOver (u : FinitePlace F) {P : Ideal (𝓞 L)}
    (hP : P ∈ IsDedekindDomain.primesOverFinset u.maximalIdeal.asIdeal (𝓞 L)) :
    PlaceLiesOver (placeOfPrimeOver u hP) u := by
  haveI := u.maximalIdeal.isMaximal
  unfold PlaceLiesOver
  rw [placeOfPrimeOver_maximalIdeal]
  exact ((mem_primesOverFinset_iff' u.maximalIdeal.ne_bot).mp hP).2

/-- **The places over `u` correspond to `primesOverFinset`**: a sum over the places of `L`
over `u` of a function of the prime is the sum over the primes of `𝓞 L` over `𝔭_u`. -/
theorem sum_placesOver_eq {M : Type*} [AddCommMonoid M] (u : FinitePlace F)
    (g : Ideal (𝓞 L) → M) :
    ∑ w ∈ placesOver L u, g w.maximalIdeal.asIdeal =
      ∑ P ∈ IsDedekindDomain.primesOverFinset u.maximalIdeal.asIdeal (𝓞 L), g P := by
  refine Finset.sum_bij (fun w _ => w.maximalIdeal.asIdeal)
    (fun w hw => mem_primesOverFinset_of_placeLiesOver (mem_placesOver.mp hw)) ?_ ?_
    (fun _ _ => rfl)
  · intro w₁ _ w₂ _ h
    exact (FinitePlace.maximalIdeal_inj _ _).mp (HeightOneSpectrum.ext h)
  · intro P hP
    exact ⟨placeOfPrimeOver u hP, mem_placesOver.mpr (placeLiesOver_placeOfPrimeOver u hP),
      placeOfPrimeOver_maximalIdeal u hP⟩

/-- `∑_{w ∣ u} e(w|u)·f(w|u) = [L : F]`. -/
theorem sum_placesOver_mul_eq_finrank (u : FinitePlace F) :
    ∑ w ∈ placesOver L u, placeRamIdx w u * placeInertiaDeg w u = finrank F L := by
  haveI := u.maximalIdeal.isMaximal
  rw [sum_placesOver_eq u (fun P => u.maximalIdeal.asIdeal.ramificationIdx' P *
    u.maximalIdeal.asIdeal.inertiaDeg' P)]
  exact Ideal.sum_ramification_inertia (𝓞 L) F L u.maximalIdeal.ne_bot

end AbcAdaptation.Tripod.Fermat.Proper.ConductorExtensionSource
