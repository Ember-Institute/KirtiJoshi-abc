/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Tower/Basic.lean and Iut/Tower/DifferentBound.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Places
import Mathlib.RingTheory.DedekindDomain.Factorization
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical

variable {K : Type*} [Field K] [NumberField K]

/-- The exponent of the prime of `v` in the normalized factors of `I`. -/
noncomputable def ordAt (I : Ideal (𝓞 K)) (v : FinitePlace K) : ℕ :=
  Multiset.count v.maximalIdeal.asIdeal (normalizedFactors I)

lemma ordAt_eq_multiplicity (I : Ideal (𝓞 K)) (hI : I ≠ 0) (v : FinitePlace K) :
    ordAt I v = multiplicity v.maximalIdeal.asIdeal I :=
  HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hI v.maximalIdeal

/-- If `𝔭_v^n` divides a nonzero ideal `I`, then `n ≤ ord_v(I)`. -/
lemma le_ordAt_of_pow_dvd (I : Ideal (𝓞 K)) (hI : I ≠ 0) (v : FinitePlace K) (n : ℕ)
    (h : v.maximalIdeal.asIdeal ^ n ∣ I) : n ≤ ordAt I v := by
  rw [ordAt_eq_multiplicity I hI v]
  have hmult := FiniteMultiplicity.of_prime_left (HeightOneSpectrum.prime v.maximalIdeal) hI
  exact hmult.pow_dvd_iff_le_multiplicity.mp h

/-- If `𝔭_v^(n+1)` does not divide a nonzero ideal `I`, then `ord_v(I) ≤ n`. -/
lemma ordAt_le_of_not_pow_dvd (I : Ideal (𝓞 K)) (hI : I ≠ 0) (v : FinitePlace K) (n : ℕ)
    (h : ¬ v.maximalIdeal.asIdeal ^ (n + 1) ∣ I) : ordAt I v ≤ n := by
  rw [ordAt_eq_multiplicity I hI v]
  by_contra hlt
  exact h (pow_dvd_of_le_multiplicity (by omega))

end AbcAdaptation.Reference.Iut
