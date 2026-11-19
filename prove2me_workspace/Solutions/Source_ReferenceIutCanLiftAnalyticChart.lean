/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original path Oka/Uniformization/FEtCovering.lean
-/
import Solutions.Source_ReferenceIutCanLiftAnalyticLocal
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

open Complex Metric Set Filter Topology Polynomial
open UpperHalfPlane hiding I I_re I_im
open scoped BigOperators

variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B] [Algebra A B]
  (ι₀ : A →ₐ[ℂ] (ℍ → ℂ))

/-- **A chart**: near `τ₁`, the points over `χ_τ` are `n` explicit holomorphic families,
separated by their values at `b₀`. -/
theorem exists_chart (hhol : ∀ a, HolH (ι₀ a)) {n : ℕ}
    (hcount : ∀ τ, Nat.card (Over B (pt ι₀ τ)) = n) (τ₁ : ℍ) (hloc : LocPres ι₀ (B := B) n τ₁) :
    ∃ V : Set ℍ, IsOpen V ∧ τ₁ ∈ V ∧ IsPreconnected V ∧
      ∃ (b₀ : B) (ε : ℝ) (σ : Fin n → ℍ → B → ℂ), 0 < ε ∧
        (∀ τ ∈ V, ∀ j k, j ≠ k → ε < ‖σ j τ b₀ - σ k τ b₀‖) ∧
        (∀ τ ∈ V, ∀ j, ∃ ψ : Over B (pt ι₀ τ), ⇑ψ.1 = σ j τ) ∧
        (∀ τ ∈ V, ∀ ψ : Over B (pt ι₀ τ), ∃ j, ⇑ψ.1 = σ j τ) ∧
        (∀ j b, DifferentiableOn ℂ (fun z ↦ σ j (ofComplex z) b) ((↑) '' V)) ∧
        (∀ j b, ContinuousOn (fun τ ↦ σ j τ b) V) ∧
        (∀ j, ContinuousOn (fun τ ↦ σ j τ b₀) V) := by
  classical
  obtain ⟨b₀, F, δ, hFm, hFn, hF, hδ, hpres⟩ := hloc
  obtain ⟨O, hOo, hτO, hOi, hOδ, r, hra, hrinj, hroot, hsurj⟩ :=
    exists_local ι₀ hhol hcount τ₁ hFm hFn hF hδ hpres
  -- the polynomial expressions `δ b = P_b(b₀)`
  have hP : ∀ b : B, ∃ P : A[X], aeval b₀ P = algebraMap A B δ * b := fun b ↦ by
    have := hpres b
    rw [Algebra.adjoin_singleton_eq_range_aeval] at this
    exact this
  choose P hPb using hP
  set σ : Fin n → ℍ → B → ℂ := fun j τ b ↦ ((P b).map (pt ι₀ τ : A →+* ℂ)).eval (r j τ) / ι₀ δ τ
  have hσψ : ∀ τ : ℍ, (τ : ℂ) ∈ O → ∀ j, ∀ ψ : Over B (pt ι₀ τ), ψ.1 b₀ = r j τ →
      ⇑ψ.1 = σ j τ := by
    intro τ hτ j ψ hψ
    funext b
    have h1 := congrArg ψ.1 (hPb b)
    rw [Over.apply_aeval, map_mul, ψ.2, hψ] at h1
    simp only [σ]
    rw [h1, pt_apply, mul_div_cancel_left₀ _ (hOδ τ hτ)]
  have hσb₀ : ∀ τ : ℍ, (τ : ℂ) ∈ O → ∀ j, σ j τ b₀ = r j τ := by
    intro τ hτ j
    obtain ⟨ψ, hψ⟩ := hsurj τ hτ j
    rw [← hσψ τ hτ j ψ hψ, hψ]
  -- separation at `τ₁`
  obtain ⟨ε, hε, hεsep⟩ : ∃ ε > 0, ∀ j k : Fin n, j ≠ k → 2 * ε < ‖r j τ₁ - r k τ₁‖ := by
    rcases (Finset.univ.offDiag : Finset (Fin n × Fin n)).eq_empty_or_nonempty with he | hne
    · refine ⟨1, one_pos, fun j k hjk ↦ ?_⟩
      have : (j, k) ∈ (Finset.univ.offDiag : Finset (Fin n × Fin n)) :=
        Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hjk⟩
      rw [he] at this; simp at this
    · set m := (Finset.univ.offDiag).inf' hne fun jk : Fin n × Fin n ↦ ‖r jk.1 τ₁ - r jk.2 τ₁‖
      have hm : 0 < m := by
        rw [Finset.lt_inf'_iff]
        rintro ⟨j, k⟩ hjk
        simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at hjk
        exact norm_pos_iff.mpr (sub_ne_zero.mpr fun h ↦ hjk (hrinj _ hτO h))
      refine ⟨m / 4, by positivity, fun j k hjk ↦ ?_⟩
      have : m ≤ ‖r j τ₁ - r k τ₁‖ := Finset.inf'_le (f := fun jk : Fin n × Fin n ↦
        ‖r jk.1 τ₁ - r jk.2 τ₁‖) (b := (j, k))
        (Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hjk⟩)
      linarith
  -- the separation persists near `τ₁`
  have hsepO : ∀ᶠ z in 𝓝 (τ₁ : ℂ), ∀ j k : Fin n, j ≠ k → ε < ‖r j z - r k z‖ := by
    rw [eventually_all]; intro j; rw [eventually_all]; intro k
    by_cases hjk : j = k
    · exact Eventually.of_forall fun _ h ↦ absurd hjk h
    · have hc : ContinuousAt (fun z ↦ ‖r j z - r k z‖) τ₁ :=
        (((hra j) _ hτO).continuousAt.sub ((hra k) _ hτO).continuousAt).norm
      have := hc.eventually (lt_mem_nhds (show ε < ‖r j τ₁ - r k τ₁‖ by
        linarith [hεsep j k hjk]))
      exact this.mono fun z hz _ ↦ hz
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (hOo.mem_nhds hτO) hsepO)
  set V : Set ℍ := (↑) ⁻¹' ball (τ₁ : ℂ) ρ
  have hVO : ∀ τ ∈ V, (τ : ℂ) ∈ O := fun τ hτ ↦ (hball hτ).1
  have himg : ((↑) : ℍ → ℂ) '' V = ball (τ₁ : ℂ) ρ := by
    ext z
    constructor
    · rintro ⟨τ, hτ, rfl⟩; exact hτ
    · intro hz
      exact ⟨⟨z, hOi z (hball hz).1⟩, hz, rfl⟩
  have hVpre : IsPreconnected V := by
    rw [← UpperHalfPlane.isEmbedding_coe.isInducing.isPreconnected_image, himg]
    exact (convex_ball _ _).isPreconnected
  have hσdiff : ∀ j b, DifferentiableOn ℂ (fun z ↦ σ j (ofComplex z) b) ((↑) '' V) := by
    intro j b
    rw [himg]
    have hsub : ball (τ₁ : ℂ) ρ ⊆ O := fun z hz ↦ (hball hz).1
    have hup : ball (τ₁ : ℂ) ρ ⊆ {z | 0 < z.im} := fun z hz ↦ hOi z (hsub hz)
    have hr' : DifferentiableOn ℂ (fun z ↦ r j z) (ball (τ₁ : ℂ) ρ) :=
      ((hra j).differentiableOn).mono hsub
    have hr'' : DifferentiableOn ℂ (fun z ↦ r j (ofComplex z : ℂ)) (ball (τ₁ : ℂ) ρ) :=
      hr'.congr fun z hz ↦ by rw [ofComplex_apply_of_im_pos (hup hz)]
    simp only [σ, eval_map, eval₂_eq_sum_range]
    refine DifferentiableOn.div ?_ ((hhol δ).mono hup) fun z hz ↦ ?_
    · refine DifferentiableOn.fun_sum fun i _ ↦ ?_
      exact ((hhol _).mono hup).mul (hr''.pow _)
    · have := hOδ (ofComplex z) (by rw [ofComplex_apply_of_im_pos (hup hz)]; exact hsub hz)
      exact this
  have hσcont : ∀ j b, ContinuousOn (fun τ ↦ σ j τ b) V := by
    intro j b
    have h1 := (hσdiff j b).continuousOn
    have h2 : ContinuousOn ((↑) : ℍ → ℂ) V := continuous_coe.continuousOn
    have := h1.comp h2 (mapsTo_image _ _)
    refine this.congr fun τ _ ↦ ?_
    simp [Function.comp_apply]
  refine ⟨V, isOpen_ball.preimage continuous_coe, by simp [V, hρ], hVpre, b₀, ε, σ, hε,
    fun τ hτ j k hjk ↦ ?_, fun τ hτ j ↦ ?_, fun τ hτ ψ ↦ ?_, hσdiff, hσcont,
    fun j ↦ hσcont j b₀⟩
  · rw [hσb₀ τ (hVO τ hτ), hσb₀ τ (hVO τ hτ)]
    exact (hball hτ).2 j k hjk
  · obtain ⟨ψ, hψ⟩ := hsurj τ (hVO τ hτ) j
    exact ⟨ψ, hσψ τ (hVO τ hτ) j ψ hψ⟩
  · obtain ⟨j, hj⟩ := hroot τ (hVO τ hτ) ψ
    exact ⟨j, hσψ τ (hVO τ hτ) j ψ hj⟩

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
