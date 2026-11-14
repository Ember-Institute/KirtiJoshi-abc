/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors
-/
import Solutions.Source_TripodLocalPlaceEmbeddingBasic

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
