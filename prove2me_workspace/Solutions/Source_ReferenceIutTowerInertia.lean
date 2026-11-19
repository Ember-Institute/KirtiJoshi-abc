/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Tower/Inertia.lean, Iut/Tripod/TpdRamIdx.lean,
and Iut/Tripod/WildRamIdx.lean
-/
import Solutions.Source_TripodRelativeValuation
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Index
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped WithZero

variable {k K : Type*} [Field k] [Field K] [NumberField K] [Algebra k K]

/-- Inertia acts trivially modulo the maximal ideal on every element integral at the place. -/
lemma valuation_sub_lt_one_of_mem_inertia {w : FinitePlace K} {σ : K ≃ₐ[k] K}
    (hσ : σ ∈ w.maximalIdeal.asIdeal.inertia (K ≃ₐ[k] K)) {x : K}
    (hx : w.maximalIdeal.valuation K x ≤ 1) :
    w.maximalIdeal.valuation K (σ x - x) < 1 := by
  let P := w.maximalIdeal
  let ν := P.valuation K
  obtain ⟨n, d, hnd⟩ := exists_primeCompl_mul_eq_of_integer P x hx
  let a : K := algebraMap (𝓞 K) K n
  let b : K := algebraMap (𝓞 K) K d
  change x * b = a at hnd
  have hmem (y : 𝓞 K) : ν (σ (y : K) - y) < 1 := by
    have hy : σ • y - y ∈ P.asIdeal := hσ y
    have heq : σ (y : K) - y = algebraMap (𝓞 K) K (σ • y - y) := by
      rw [map_sub] <;> rfl
    rw [heq]
    exact (valuation_lt_one_iff_mem (K := K) P _).mpr hy
  have hb : ν b = 1 := (valuation_eq_one_iff_notMem P).mpr d.2
  have hσb : ν (σ b) = 1 := by
    have hlt : ν (σ b - b) < ν b := by
      rw [hb]
      exact hmem d
    calc
      ν (σ b) = ν ((σ b - b) + b) := by rw [sub_add_cancel]
      _ = ν b := Valuation.map_add_eq_of_lt_right ν hlt
      _ = 1 := hb
  have hσnd : σ x * σ b = σ a := by rw [← map_mul, hnd]
  have hdiff : (σ x - x) * σ b = (σ a - a) - x * (σ b - b) := by
    rw [sub_mul, hσnd, ← hnd]
    ring
  have hxb : ν (x * (σ b - b)) < 1 := by
    rw [map_mul]
    calc
      ν x * ν (σ b - b) ≤ 1 * ν (σ b - b) := mul_le_mul_left hx _
      _ < 1 := by rw [one_mul]; exact hmem d
  have hlt : ν ((σ x - x) * σ b) < 1 := by
    rw [hdiff]
    exact (Valuation.map_sub ν _ _).trans_lt (max_lt (hmem n) hxb)
  simpa only [map_mul, hσb, mul_one] using hlt

variable [NumberField k] [IsGalois k K]

/-- The relative ramification index equals the order of the inertia group. -/
theorem relRamIdx_eq_card_inertia {w : FinitePlace K} {v : FinitePlace k}
    (hwv : FinitePlace.LiesOver w v) :
    Tripod.relRamIdx w v = Nat.card (w.maximalIdeal.asIdeal.inertia (K ≃ₐ[k] K)) := by
  haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hwv
  haveI : v.maximalIdeal.asIdeal.IsMaximal :=
    v.maximalIdeal.isPrime.isMaximal v.maximalIdeal.ne_bot
  haveI : Finite (𝓞 k ⧸ v.maximalIdeal.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ v.maximalIdeal.ne_bot
  letI : FiniteDimensional k K := Module.Finite.of_restrictScalars_finite ℚ k K
  letI : Module.Finite (𝓞 k) (𝓞 K) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 k) (𝓞 K)
  unfold Tripod.relRamIdx
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := K ≃ₐ[k] K)
      v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal
      (K ≃ₐ[k] K),
    Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.maximalIdeal.ne_bot]

/-- The relative ramification index is one if every inertia automorphism is the identity. -/
theorem relRamIdx_eq_one_of_inertia_trivial {v : FinitePlace K} {u : FinitePlace k}
    (hvu : FinitePlace.LiesOver v u)
    (hfix : ∀ σ : K ≃ₐ[k] K, (∀ x : K, v.maximalIdeal.valuation K x ≤ 1 →
      v.maximalIdeal.valuation K (σ x - x) < 1) → σ = 1) :
    Tripod.relRamIdx v u = 1 := by
  rw [relRamIdx_eq_card_inertia hvu, Subgroup.card_eq_one, eq_bot_iff]
  intro σ hσ
  exact Subgroup.mem_bot.mpr
    (hfix σ fun _ hx => valuation_sub_lt_one_of_mem_inertia hσ hx)

/-- The relative ramification index divides the degree of a Galois extension. -/
theorem relRamIdx_dvd_finrank {w : FinitePlace K} {v : FinitePlace k}
    (hwv : FinitePlace.LiesOver w v) :
    Tripod.relRamIdx w v ∣ Module.finrank k K := by
  letI : FiniteDimensional k K := Module.Finite.of_restrictScalars_finite ℚ k K
  rw [relRamIdx_eq_card_inertia hwv, ← IsGalois.card_aut_eq_finrank k K]
  exact Subgroup.card_subgroup_dvd_card _

end AbcAdaptation.Reference.Iut
