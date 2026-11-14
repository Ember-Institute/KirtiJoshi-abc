/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors
-/
import Solutions.Source_TripodLocalPlaceEmbeddingDegree

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
