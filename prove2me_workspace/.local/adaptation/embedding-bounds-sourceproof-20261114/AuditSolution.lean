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
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Definitions.Def_FermatLocalBelyi
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic

/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors
-/

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

/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors
-/

namespace AbcAdaptation.Tripod.Local

open NumberField IsDedekindDomain HeightOneSpectrum Polynomial

variable {p : ℕ} [hp : Fact p.Prime]
variable {F : Type*} [Field F] [NumberField F]

/-- The norm of `𝔭_τ` is a positive power of `p`. -/
theorem exists_absNorm_eq_pow {v : HeightOneSpectrum (𝓞 F)} (hpv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    ∃ j : ℕ, 0 < j ∧ Ideal.absNorm v.asIdeal = p ^ j := by
  have hle : Ideal.span {((p : ℕ) : 𝓞 F)} ≤ v.asIdeal := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hpv
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
  rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 F)), Algebra.norm_algebraMap,
    Int.natAbs_pow, Int.natAbs_natCast] at hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
  refine ⟨j, Nat.pos_of_ne_zero fun h0 => ?_, hj⟩
  rw [h0, pow_zero, Ideal.absNorm_eq_one_iff] at hj
  exact v.isPrime.ne_top hj

/-- `‖τ ·‖ ^ N = adicAbv` at `𝔭_τ` for a natural number `0 < N ≤ [F : ℚ]`. -/
theorem exists_pow_eq_adicAbv (τ : F →+* PadicAlgCl p) :
    ∃ N : ℕ, 0 < N ∧ N ≤ Module.finrank ℚ F ∧
      ∀ y : F, adicAbv F (placeOfRingHom τ) y = ‖τ y‖ ^ N := by
  set v := placeOfRingHom τ with hv
  obtain ⟨c, hc, hcw⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp (isEquiv_ringHomAbv τ)
  have hpv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := natCast_p_mem_primeOfRingHom τ
  obtain ⟨j, hj, hjN⟩ := exists_absNorm_eq_pow hpv
  have hp0 : ((p : ℕ) : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  -- the multiplicity `m` of `𝔭_τ` in `p`
  set m := multiplicity v.asIdeal (Ideal.span {((p : ℕ) : 𝓞 F)}) with hm
  have hmp := HeightOneSpectrum.embedding_mul_absNorm (K := F) v hp0
  rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity
      (mt Submodule.span_singleton_eq_bot.mp hp0), map_pow, hjN, ← hm,
    FinitePlace.norm_embedding] at hmp
  -- evaluate the equivalence at `p`
  have hcp := congrFun hcw ((p : ℕ) : F)
  simp only [ringHomAbv_apply, norm_ringHom_natCast_p] at hcp
  have hpF : algebraMap (𝓞 F) F ((p : ℕ) : 𝓞 F) = ((p : ℕ) : F) := by simp
  rw [hpF] at hmp
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hval' : adicAbv F v ((p : ℕ) : F) * (p : ℝ) ^ (j * m) = 1 := by
    push_cast at hmp ⊢
    rw [pow_mul]
    exact hmp
  have hval : adicAbv F v ((p : ℕ) : F) = ((p : ℝ) ^ (j * m))⁻¹ :=
    eq_inv_of_mul_eq_one_left hval'
  have hceq : c = (j * m : ℕ) := by
    rw [hval] at hcp
    have h1 : Real.log (((p : ℝ)⁻¹) ^ c) = Real.log (((p : ℝ) ^ (j * m))⁻¹) := by rw [hcp]
    rw [Real.log_rpow (by positivity), Real.log_inv, Real.log_inv, Real.log_pow] at h1
    have hlogp : 0 < Real.log p := Real.log_pos hpR
    have h2 : c * Real.log p = ((j * m : ℕ) : ℝ) * Real.log p := by linarith
    exact mul_right_cancel₀ hlogp.ne' h2
  refine ⟨j * m, ?_, ?_, fun y => ?_⟩
  · have : (0 : ℝ) < ((j * m : ℕ) : ℝ) := hceq ▸ hc
    exact_mod_cast this
  · -- `N(𝔭)^m ∣ N(p) = p^[F:ℚ]`
    have hdiv : v.asIdeal ^ m ∣ Ideal.span {((p : ℕ) : 𝓞 F)} := pow_multiplicity_dvd _ _
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdiv)
    rw [map_pow, hjN, Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 F)),
      Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast, ← pow_mul] at hdvd
    have := (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp hdvd
    rwa [RingOfIntegers.rank] at this
  · have := congrFun hcw y
    simp only [ringHomAbv_apply] at this
    rw [← this, hceq, Real.rpow_natCast]


end AbcAdaptation.Tripod.Local

/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors
-/

namespace AbcAdaptation.Tripod.Local

open NumberField IsDedekindDomain HeightOneSpectrum Polynomial

variable {p : ℕ} [hp : Fact p.Prime]
variable {F : Type*} [Field F] [NumberField F]

/-- **Every prime of `𝓞 F` over `p` is `𝔭_τ` for some `τ : F → ℚ̄_p`.** -/
theorem exists_placeOfRingHom_eq {v : HeightOneSpectrum (𝓞 F)}
    (hpv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) : ∃ τ : F →+* PadicAlgCl p, placeOfRingHom τ = v := by
  classical
  by_contra hne
  push Not at hne
  -- prime avoidance: some `y ∈ 𝔭` lies in no `𝔭_τ`
  have hnot : ¬ ((v.asIdeal : Set (𝓞 F)) ⊆ ⋃ τ ∈ (Finset.univ : Finset (F →+* PadicAlgCl p)),
      (primeOfRingHom τ : Set (𝓞 F))) := by
    intro hsub
    obtain ⟨τ, -, hτ⟩ := (Ideal.subset_union_prime (s := Finset.univ)
      (f := fun τ => primeOfRingHom τ) (Classical.arbitrary _) (Classical.arbitrary _)
      (fun τ _ _ _ => inferInstance)).mp hsub
    have hmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
    have heq : v.asIdeal = primeOfRingHom τ :=
      hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hτ
    exact hne τ (HeightOneSpectrum.ext heq.symm)
  obtain ⟨y, hyv, hyτ⟩ := Set.not_subset.mp hnot
  simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion, SetLike.mem_coe, not_exists] at hyτ
  have hone : ∀ τ : F →+* PadicAlgCl p, ‖τ y‖ = 1 := fun τ => norm_eq_one_of_notMem (hyτ τ)
  -- the norm of `y`
  have hnorm := Algebra.norm_eq_prod_embeddings ℚ (PadicAlgCl p) (y : F)
  have hnorm1 : ‖algebraMap ℚ (PadicAlgCl p) (Algebra.norm ℚ (y : F))‖ = 1 := by
    rw [hnorm, norm_prod]
    exact Finset.prod_eq_one fun σ _ => hone σ.toRingHom
  rw [← Algebra.coe_norm_int] at hnorm1
  -- `p` divides the norm of `y`
  have hle : Ideal.span {y} ≤ v.asIdeal := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hyv
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
  obtain ⟨j, hj, hjN⟩ := exists_absNorm_eq_pow hpv
  rw [hjN, Ideal.absNorm_span_singleton] at hdvd
  have hpdvd : (p : ℤ) ∣ Algebra.norm ℤ y := by
    have : p ∣ (Algebra.norm ℤ y).natAbs := (dvd_pow_self p hj.ne').trans hdvd
    exact Int.natCast_dvd.mpr this
  obtain ⟨k, hk⟩ := hpdvd
  rw [hk] at hnorm1
  have : ‖algebraMap ℚ (PadicAlgCl p) (((p : ℤ) * k : ℤ) : ℚ)‖ < 1 := by
    have h1 : algebraMap ℚ (PadicAlgCl p) (((p : ℤ) * k : ℤ) : ℚ) =
        algebraMap ℚ_[p] (PadicAlgCl p) ((p : ℚ_[p]) * (k : ℚ_[p])) := by
      simp
    rw [h1, norm_algebraMap', norm_mul, Padic.norm_p]
    have hk1 : ‖(k : ℚ_[p])‖ ≤ 1 := Padic.norm_int_le_one k
    have hpinv : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
    calc (p : ℝ)⁻¹ * ‖(k : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hk1 (by positivity)
      _ < 1 := by rw [mul_one]; exact hpinv
  linarith

/-- **Finite places of a number field and embeddings into `ℚ̄_p`**: for a finite place `w` of
`F` whose prime contains `p`, there are `τ : F → ℚ̄_p` and `0 < N ≤ [F : ℚ]` with
`w y = ‖τ y‖ ^ N` for all `y`. -/
theorem exists_ringHom_padicAlgCl_eq_pow (w : FinitePlace F)
    (hpw : ((p : ℕ) : 𝓞 F) ∈ w.maximalIdeal.asIdeal) :
    ∃ τ : F →+* PadicAlgCl p, ∃ N : ℕ, 0 < N ∧ N ≤ Module.finrank ℚ F ∧
      ∀ y : F, w y = ‖τ y‖ ^ N := by
  obtain ⟨τ, hτ⟩ := exists_placeOfRingHom_eq hpw
  obtain ⟨N, hN, hNle, hNeq⟩ := exists_pow_eq_adicAbv τ
  refine ⟨τ, N, hN, hNle, fun y => ?_⟩
  rw [← FinitePlace.norm_embedding_eq, FinitePlace.norm_embedding, ← hτ, hNeq]

end AbcAdaptation.Tripod.Local

/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors
-/

/-!
# Bounds at places from bounds at embeddings

A point of `U_ℙ(ℚ̄)` of degree `d` determines `d` points of `U_ℙ(ℚ̄_v)` for every place `v` of
`ℚ` (its images under the embeddings of its field of definition); compactly bounded subsets
are defined by conditions on these ([GenEll], Example 1.3 (ii)). This file translates such
conditions into conditions on the absolute values of the number field at its places above
`v`, in the normalisation of Mathlib's `NumberField.FinitePlace` / `InfinitePlace`:

* `Heights.Local.abs_log_finitePlace_le`: if `|log ‖τ λ‖| ≤ c` for all `τ : F → ℚ̄_p`, then
  `|log w λ| ≤ [F : ℚ] c` for every finite place `w` of `F` over `p`;
* `Heights.Local.abs_log_infinitePlace_le`: if `|log |σ λ|| ≤ c` for all `σ : F → ℂ`, then
  `|log w λ| ≤ c` for every infinite place `w`.
-/

namespace AbcAdaptation.Tripod.Local

open NumberField

variable {F : Type*} [Field F] [NumberField F]

/-- Bounds at all embeddings into `ℚ̄_p` give bounds at all finite places over `p`. -/
theorem abs_log_finitePlace_le {p : ℕ} [Fact p.Prime] {c : ℝ} (hc : 0 ≤ c) {y : F}
    (hy : ∀ τ : F →+* PadicAlgCl p, |Real.log ‖τ y‖| ≤ c) (w : FinitePlace F)
    (hpw : ((p : ℕ) : 𝓞 F) ∈ w.maximalIdeal.asIdeal) :
    |Real.log (w y)| ≤ Module.finrank ℚ F * c := by
  obtain ⟨τ, N, hN, hNle, hw⟩ := exists_ringHom_padicAlgCl_eq_pow w hpw
  rw [hw y, Real.log_pow, abs_mul, Nat.abs_cast]
  exact mul_le_mul (by exact_mod_cast hNle) (hy τ) (abs_nonneg _) (Nat.cast_nonneg _)

/-- Bounds at all complex embeddings give bounds at all infinite places. -/
theorem abs_log_infinitePlace_le {c : ℝ} {y : F} (hy : ∀ σ : F →+* ℂ, |Real.log ‖σ y‖| ≤ c)
    (w : InfinitePlace F) : |Real.log (w y)| ≤ c := by
  rw [← InfinitePlace.norm_embedding_eq w y]
  exact hy _

end AbcAdaptation.Tripod.Local

/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Source: Heights/Local/Bounded.lean and Iut/Tripod/GeneralPosition.lean:170-205.
The explicit extension below transfers every embedding of the actual image field
through the inclusion into the same full point field used by LocalBounds.
-/

set_option autoImplicit false

open NumberField
open scoped IntermediateField

namespace AbcAdaptation.Tripod.Local

/-- The algebraically closed target extends every embedding. -/
theorem exists_ringHom_extension {F L E : Type*} [Field F] [Field L] [Field E]
    [Algebra F L] [Algebra.IsAlgebraic F L] [IsAlgClosed E] (σ : F →+* E) :
    ∃ τ : L →+* E, ∀ a : F, τ (algebraMap F L a) = σ a := by
  letI : Algebra F E := σ.toAlgebra
  let τ : L →ₐ[F] E := IsAlgClosed.lift
  exact ⟨τ.toRingHom, fun a => τ.commutes a⟩

/-- Restriction of the full all-embeddings bound to the actual image subfield.
Both evaluations and the same constant occur in the conclusion. -/
theorem allEmbedding_bounds_descend (F L : IntermediateField ℚ Tripod.Qbar)
    [FiniteDimensional ℚ L] (hFL : F ≤ L)
    {E : Type*} [NormedField E] [IsAlgClosed E]
    (a : F) (b : L) (hab : (a : Tripod.Qbar) = (b : Tripod.Qbar)) (c : ℝ)
    (hb : ∀ τ : L →+* E,
      |Real.log ‖τ b‖| ≤ c ∧ |Real.log ‖τ b - 1‖| ≤ c) :
    ∀ σ : F →+* E, |Real.log ‖σ a‖| ≤ c ∧ |Real.log ‖σ a - 1‖| ≤ c := by
  letI : Algebra F L := (IntermediateField.inclusion hFL).toRingHom.toAlgebra
  letI : Algebra.IsAlgebraic F L := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  have hab' : algebraMap F L a = b := Subtype.ext hab
  intro σ
  obtain ⟨τ, hτ⟩ := exists_ringHom_extension (L := L) σ
  have ha : τ b = σ a := by rw [← hab', hτ]
  simpa only [ha] using hb τ

end AbcAdaptation.Tripod.Local

namespace AbcAdaptation.Tripod.Fermat.Proper

variable {N : ℕ}

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Source-faithful all-place bridge with the fixed `(d+1) * max c 0` scale. -/
theorem embeddingBoundsToSet_source (M : Model N) (hRF : ResiduesFinite M) :
    EmbeddingBoundsToSet M := by
  intro x φ d c hxd hx
  obtain ⟨hφ, h0, h1, hC, hp⟩ := hx
  letI : FiniteDimensional ℚ x.P.ResidueField := hRF x.P
  letI : FiniteDimensional ℚ x.fieldOf :=
    x.σ.toRatAlgHom.equivFieldRange.toLinearEquiv.finiteDimensional
  let z : Tripod.Pt := belyiImage M φ x
  let a : Tripod.fieldOf z.1 := Tripod.gen z.1
  let b : x.fieldOf := evalInField M x φ hφ
  have hz : z = ⟨x.eval φ hφ, h0, h1⟩ := belyiImage_eq M φ x hφ h0 h1
  have hab : (a : Tripod.Qbar) = (b : Tripod.Qbar) := by
    change z.1 = x.eval φ hφ
    rw [hz]
  have hFL : Tripod.fieldOf z.1 ≤ x.fieldOf :=
    belyiImage_field_le M φ x ⟨hφ, h0, h1⟩
  have hdeg : Module.finrank ℚ (Tripod.fieldOf z.1) ≤ d :=
    (IntermediateField.finrank_le_of_le_right hFL).trans hxd
  have hC' := Local.allEmbedding_bounds_descend (Tripod.fieldOf z.1) x.fieldOf
    hFL a b hab c hC
  have hp' := Local.allEmbedding_bounds_descend (Tripod.fieldOf z.1) x.fieldOf
    hFL a b hab c hp
  have hc0 : 0 ≤ max c 0 := le_max_right _ _
  have hdle : (Module.finrank ℚ (Tripod.fieldOf z.1) : ℝ) * max c 0 ≤
      (d + 1) * max c 0 :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hdeg.trans (Nat.le_succ d)) hc0
  have hle1 : max c 0 ≤ (d + 1) * max c 0 := by
    have hd1 : (1 : ℝ) ≤ d + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    nlinarith
  change z ∈ (localCompactSet d c).set
  refine ⟨fun v hv => ?_, fun w => ?_⟩
  · have hchar : Tripod.residueChar v = 2 := Finset.mem_singleton.mp hv
    have hmem' : ((Tripod.residueChar v : ℕ) : 𝓞 (Tripod.fieldOf z.1)) ∈
        v.maximalIdeal.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact ringChar.Nat.cast_ringChar
    have hmem : ((2 : ℕ) : 𝓞 (Tripod.fieldOf z.1)) ∈ v.maximalIdeal.asIdeal := by
      simpa only [hchar] using hmem'
    have hv1 := Local.abs_log_finitePlace_le hc0 (y := a)
      (fun τ => ((hp' τ).1).trans (le_max_left _ _)) v hmem
    have hv2 := Local.abs_log_finitePlace_le hc0 (y := a - 1)
      (fun τ => by
        rw [map_sub, map_one]
        exact ((hp' τ).2).trans (le_max_left _ _)) v hmem
    exact ⟨hv1.trans hdle, hv2.trans hdle⟩
  · have hw1 := Local.abs_log_infinitePlace_le (y := a)
      (fun σ => ((hC' σ).1).trans (le_max_left _ (0 : ℝ))) w
    have hw2 := Local.abs_log_infinitePlace_le (y := a - 1)
      (fun σ => by
        rw [map_sub, map_one]
        exact ((hC' σ).2).trans (le_max_left _ (0 : ℝ))) w
    exact ⟨hw1.trans hle1, hw2.trans hle1⟩

end AbcAdaptation.Tripod.Fermat.Proper

/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors
-/

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

theorem closedEmbeddingSource {N : ℕ} (M : Model N)
    (hRF : ResiduesFinite M) : EmbeddingBoundsToSet M :=
  embeddingBoundsToSet_source M hRF

end AbcAdaptation.Tripod.Fermat.Proper

theorem solution : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N),
  AbcAdaptation.Tripod.Fermat.Proper.ResiduesFinite M → AbcAdaptation.Tripod.Fermat.Proper.EmbeddingBoundsToSet M :=
  AbcAdaptation.Tripod.Fermat.Proper.closedEmbeddingSource

theorem PlatformOriginalType : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N),
  AbcAdaptation.Tripod.Fermat.Proper.ResiduesFinite M → AbcAdaptation.Tripod.Fermat.Proper.EmbeddingBoundsToSet M := solution

open Lean
run_meta do
  let a ← getConstInfo `solution
  let e ← getConstInfo `PlatformOriginalType
  unless ← Lean.Meta.isDefEq a.type e.type do throwError "Original platform type differs"
  let axs ← collectAxioms `solution
  for ax in axs do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do throwError "Unexpected solution axiom {ax}"
  IO.FS.writeFile ".local/adaptation/embedding-bounds-sourceproof-20261114/solution-type-axioms.json" (Json.pretty (Json.mkObj [("type",Json.str (← Lean.Meta.ppExpr a.type).pretty),("axioms",toJson (axs.map toString)),("original_type_equal",Json.bool true)]))
