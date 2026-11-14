/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors
-/
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Set

namespace AbcAdaptation.Tripod.Local

open NumberField IsDedekindDomain HeightOneSpectrum Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Ultrametric root bound**: in an ultrametric normed field, a root of a monic polynomial
with coefficients of norm `≤ 1` has norm `≤ 1`. -/
theorem norm_le_one_of_monic_of_eval_eq_zero {E : Type*} [NormedField E] [IsUltrametricDist E]
    {P : E[X]} (hP : P.Monic) (hc : ∀ i, ‖P.coeff i‖ ≤ 1) {x : E} (hx : P.eval x = 0) :
    ‖x‖ ≤ 1 := by
  by_contra hlt
  push Not at hlt
  set n := P.natDegree with hn
  have hn0 : n ≠ 0 := by
    intro h0
    have h1 : P = 1 := hP.natDegree_eq_zero.mp h0
    rw [h1, eval_one] at hx
    exact one_ne_zero hx
  have hsum : P.eval x = x ^ n + ∑ i ∈ Finset.range n, P.coeff i * x ^ i := by
    conv_lhs => rw [hP.as_sum]
    simp [eval_finsetSum, hn]
  rw [hsum, add_eq_zero_iff_eq_neg] at hx
  have hbound : ‖∑ i ∈ Finset.range n, P.coeff i * x ^ i‖ ≤ ‖x‖ ^ (n - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow]
    have hi' : i ≤ n - 1 := by
      have := Finset.mem_range.mp hi
      omega
    calc ‖P.coeff i‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ (n - 1) :=
          mul_le_mul (hc i) (pow_le_pow_right₀ hlt.le hi') (by positivity) zero_le_one
      _ = ‖x‖ ^ (n - 1) := one_mul _
  have h1 : ‖x‖ ^ n ≤ ‖x‖ ^ (n - 1) := by
    rw [← norm_pow, hx, norm_neg]
    exact hbound
  have h2 : ‖x‖ ^ (n - 1) < ‖x‖ ^ n := pow_lt_pow_right₀ hlt (by omega)
  linarith

variable {F : Type*} [Field F] [NumberField F]

/-- The image of an algebraic integer under a ring homomorphism `F → ℚ̄_p` has norm `≤ 1`. -/
theorem norm_ringHom_le_one (τ : F →+* PadicAlgCl p) (y : 𝓞 F) : ‖τ y‖ ≤ 1 := by
  have hint : IsIntegral ℤ y := RingOfIntegers.isIntegral y
  set P := (minpoly ℤ y).map (Int.castRingHom (PadicAlgCl p)) with hP
  refine norm_le_one_of_monic_of_eval_eq_zero (P := P)
    ((minpoly.monic hint).map (Int.castRingHom (PadicAlgCl p))) (fun i => ?_) ?_
  · rw [hP, coeff_map, eq_intCast]
    exact IsUltrametricDist.norm_intCast_le_one _ _
  · rw [hP, eval_map]
    have h0 : eval₂ (algebraMap ℤ (𝓞 F)) y (minpoly ℤ y) = 0 := minpoly.aeval ℤ y
    have h1 := congrArg (τ.comp (algebraMap (𝓞 F) F)) h0
    rw [hom_eval₂, map_zero] at h1
    convert h1 using 2
    all_goals first | exact RingHom.ext_int _ _ | rfl

/-- The absolute value `y ↦ ‖τ y‖` on `F` defined by `τ : F → ℚ̄_p`. -/
noncomputable def ringHomAbv (τ : F →+* PadicAlgCl p) : AbsoluteValue F ℝ :=
  (NormedField.toAbsoluteValue (PadicAlgCl p)).comp τ.injective

@[simp] theorem ringHomAbv_apply (τ : F →+* PadicAlgCl p) (y : F) :
    ringHomAbv τ y = ‖τ y‖ := rfl

/-- `‖τ p‖ = p⁻¹`. -/
theorem norm_ringHom_natCast_p (τ : F →+* PadicAlgCl p) : ‖τ (p : F)‖ = (p : ℝ)⁻¹ := by
  rw [map_natCast]
  have : ((p : ℕ) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) := by
    simp
  rw [this, norm_algebraMap', Padic.norm_p]

/-- The prime ideal `𝔭_τ = {y ∈ 𝓞 F | ‖τ y‖ < 1}` defined by `τ : F → ℚ̄_p`. -/
noncomputable def primeOfRingHom (τ : F →+* PadicAlgCl p) : Ideal (𝓞 F) where
  carrier := {y | ‖τ y‖ < 1}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' c y hy := by
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at hy ⊢
    calc ‖τ c‖ * ‖τ y‖ ≤ 1 * ‖τ y‖ :=
          mul_le_mul_of_nonneg_right (norm_ringHom_le_one τ c) (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hy

theorem mem_primeOfRingHom {τ : F →+* PadicAlgCl p} {y : 𝓞 F} :
    y ∈ primeOfRingHom τ ↔ ‖τ y‖ < 1 := Iff.rfl

theorem natCast_p_mem_primeOfRingHom (τ : F →+* PadicAlgCl p) :
    ((p : ℕ) : 𝓞 F) ∈ primeOfRingHom τ := by
  rw [mem_primeOfRingHom]
  have : τ (((p : ℕ) : 𝓞 F) : F) = τ (p : F) := by simp
  rw [this, norm_ringHom_natCast_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

instance (τ : F →+* PadicAlgCl p) : (primeOfRingHom τ).IsPrime where
  ne_top' := by
    rw [Ne, Ideal.eq_top_iff_one, mem_primeOfRingHom]
    simp
  mem_or_mem' {a b} hab := by
    rw [mem_primeOfRingHom, mem_primeOfRingHom]
    rw [mem_primeOfRingHom] at hab
    simp only [map_mul, norm_mul] at hab
    by_contra h
    push Not at h
    have := mul_le_mul h.1 h.2 zero_le_one (norm_nonneg _)
    rw [one_mul] at this
    linarith

theorem primeOfRingHom_ne_bot (τ : F →+* PadicAlgCl p) : primeOfRingHom τ ≠ ⊥ := by
  intro h
  have := natCast_p_mem_primeOfRingHom τ
  rw [h, Ideal.mem_bot] at this
  exact (Nat.cast_ne_zero.mpr hp.out.ne_zero) this

/-- The height one prime `𝔭_τ`. -/
noncomputable def placeOfRingHom (τ : F →+* PadicAlgCl p) : HeightOneSpectrum (𝓞 F) :=
  ⟨primeOfRingHom τ, inferInstance, primeOfRingHom_ne_bot τ⟩

/-- For `d ∉ 𝔭_τ`, `‖τ d‖ = 1`. -/
theorem norm_eq_one_of_notMem {τ : F →+* PadicAlgCl p} {d : 𝓞 F}
    (hd : d ∉ primeOfRingHom τ) : ‖τ d‖ = 1 := by
  rw [mem_primeOfRingHom, not_lt] at hd
  exact le_antisymm (norm_ringHom_le_one τ d) hd

/-- For `y ∈ F` with `v`-adic valuation `≤ 1` there are `n ∈ 𝓞 F` and `d ∉ 𝔭` with
`y d = n`. -/
theorem valuation_le_one_iff_norm_le_one (τ : F →+* PadicAlgCl p) (y : F) :
    (placeOfRingHom τ).valuation F y ≤ 1 ↔ ‖τ y‖ ≤ 1 := by
  set v := placeOfRingHom τ with hv
  constructor
  · intro hy
    obtain ⟨n, d, hnd⟩ := exists_primeCompl_mul_eq_of_integer v y hy
    have hd : ‖τ (algebraMap (𝓞 F) F d)‖ = 1 := norm_eq_one_of_notMem d.2
    have h := congrArg (fun z => ‖τ z‖) hnd
    simp only [map_mul, norm_mul, hd, mul_one] at h
    rw [h]
    exact norm_ringHom_le_one τ n
  · intro hy
    by_contra hlt
    push Not at hlt
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp at hlt
    have hinv : v.valuation F y⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ hlt
    obtain ⟨n, d, hnd⟩ := exists_primeCompl_mul_eq_of_integer v y⁻¹ hinv.le
    have hn : n ∈ v.asIdeal := by
      rw [← intValuation_lt_one_iff_mem, ← valuation_of_algebraMap (K := F)]
      have : v.valuation F (algebraMap (𝓞 F) F n) = v.valuation F y⁻¹ := by
        rw [← hnd, map_mul, valuation_of_algebraMap,
          (intValuation_eq_one_iff_mem_primeCompl v d).mpr d.2, mul_one]
      rw [this]
      exact hinv
    have hn' : ‖τ (algebraMap (𝓞 F) F n)‖ < 1 := hn
    have hd : ‖τ (algebraMap (𝓞 F) F d)‖ = 1 := norm_eq_one_of_notMem d.2
    have h := congrArg (fun z => ‖τ z‖) hnd
    simp only [map_mul, norm_mul, hd, mul_one, map_inv₀, norm_inv] at h
    rw [← h] at hn'
    have hpos : 0 < ‖τ y‖ := norm_pos_iff.mpr ((map_ne_zero τ).mpr hy0)
    have : 1 < ‖τ y‖ := by
      rw [inv_lt_one₀ hpos] at hn'
      exact hn'
    linarith

/-- The absolute value `adicAbv` at `𝔭_τ` and `‖τ ·‖` have the same unit ball. -/
theorem adicAbv_le_one_iff (τ : F →+* PadicAlgCl p) (y : F) :
    adicAbv F (placeOfRingHom τ) y ≤ 1 ↔ ‖τ y‖ ≤ 1 := by
  rw [adicAbv_def, ← valuation_le_one_iff_norm_le_one τ y]
  have := WithZeroMulInt.toNNReal_le_one_iff (m := (placeOfRingHom τ).valuation F y)
    (one_lt_absNorm_nnreal (placeOfRingHom τ))
  exact_mod_cast this

/-- `adicAbv` at `𝔭_τ` is equivalent to `‖τ ·‖`. -/
theorem isEquiv_ringHomAbv (τ : F →+* PadicAlgCl p) :
    (ringHomAbv τ).IsEquiv (adicAbv F (placeOfRingHom τ)) := by
  intro x y
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hA : 0 < ringHomAbv τ y := (ringHomAbv τ).pos hy
  have hB : 0 < adicAbv F (placeOfRingHom τ) y := (adicAbv F (placeOfRingHom τ)).pos hy
  rw [← div_le_one hA, ← div_le_one hB, ← map_div₀, ← map_div₀, ringHomAbv_apply,
    adicAbv_le_one_iff]


end AbcAdaptation.Tripod.Local
