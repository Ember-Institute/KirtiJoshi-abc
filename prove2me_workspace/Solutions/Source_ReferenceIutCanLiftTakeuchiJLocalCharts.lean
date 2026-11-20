/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/S1/JOrb.lean, lines 578–783
-/
import Solutions.Source_ReferenceIutCanLiftTakeuchiCayleyAction
import Solutions.Source_ReferenceIutCanLiftTakeuchiOrbifoldCover
import Solutions.Source_ReferenceIutCanLiftTakeuchiRotationLocalForm

set_option autoImplicit false

open AbcAdaptation.Reference
open Filter Metric Set Topology UpperHalfPlane
open scoped MatrixGroups Topology UpperHalfPlane

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi

/-! ### Orbifold charts of `j` at a point of `ℍ` -/

/-- Orbifold chart data of `jC` at `τ₀`: an `OrbChart` over `jC τ₀` whose domain `U` is a
neighbourhood of `τ₀` in `ℍ`, stable under the stabiliser of `τ₀`, meeting its translates only
through the stabiliser, and whose coordinate `u` is a local coordinate at `τ₀`. -/
structure JChartData (τ₀ : ℂ) (e : ℕ) (r : ℝ) (U : Set ℂ) (u v : ℂ → ℂ) : Prop where
  chart : OrbChart jC (jC τ₀) e r U u v
  mem : τ₀ ∈ U
  sub : U ⊆ upper
  analyticAt : AnalyticAt ℂ u τ₀
  u_self : u τ₀ = 0
  deriv_ne : deriv u τ₀ ≠ 0
  stab : ∀ γ : SL(2, ℤ), ∀ z ∈ U, smulC γ z ∈ U → smulC γ τ₀ = τ₀
  inv : ∀ γ : SL(2, ℤ), smulC γ τ₀ = τ₀ → ∀ z ∈ U, smulC γ z ∈ U

/-- Proper discontinuity: a neighbourhood of `τ₀` meeting its translates only through the
stabiliser of `τ₀`. -/
theorem exists_nhds_stab (τ₀ : ℍ) :
    ∃ N ∈ 𝓝 τ₀, ∀ γ : SL(2, ℤ), ∀ z ∈ N, γ • z ∈ N → γ • τ₀ = τ₀ := by
  obtain ⟨U, hU, hUγ⟩ := ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self 𝒮ℒ τ₀
  refine ⟨U, hU, fun γ z hz hγz ↦ ?_⟩
  let g : 𝒮ℒ := ⟨Matrix.SpecialLinearGroup.mapGL ℝ γ, γ, rfl⟩
  have hg : ∀ x : ℍ, g • x = γ • x := fun x ↦ rfl
  have := hUγ g ⟨γ • z, ⟨z, hz, hg z⟩, hγz⟩
  rwa [hg] at this

theorem smulC_eq_self_iff {γ : SL(2, ℤ)} {τ₀ : ℍ} : smulC γ τ₀ = τ₀ ↔ γ • τ₀ = τ₀ := by
  rw [smulC_coe]
  exact ⟨fun h ↦ UpperHalfPlane.ext h, fun h ↦ by rw [h]⟩

/-- **Orbifold charts of `j`.** If the stabiliser of `τ₀` acts in the Cayley coordinate by `e`-th
roots of unity, one of which has order exactly `e`, then `j` has an orbifold chart of order `e`
at `τ₀`. -/
theorem exists_jChartData (τ₀ : ℍ) {e : ℕ} (he : 0 < e)
    (hS : ∀ γ : SL(2, ℤ), γ • τ₀ = τ₀ → cmul γ τ₀ ^ e = 1)
    {γ₀ : SL(2, ℤ)} (hγ₀ : γ₀ • τ₀ = τ₀) (hR : ∀ m : ℕ, cmul γ₀ τ₀ ^ m = 1 → e ∣ m) :
    ∃ r > 0, ∃ U u v, JChartData (τ₀ : ℂ) e r U u v := by
  set τ : ℂ := ↑τ₀
  have hτ : 0 < τ.im := τ₀.im_pos
  set w := jC τ
  set F : ℂ → ℂ := fun s ↦ jC (cayInv τ s)
  -- proper discontinuity
  obtain ⟨N, hN, hNγ⟩ := exists_nhds_stab τ₀
  set N' : Set ℂ := (↑) '' N
  have hN' : N' ∈ 𝓝 τ := by
    have := isOpenEmbedding_coe.isOpenMap.image_mem_nhds hN
    simpa using this
  have hN'mem : ∀ z (hz : 0 < z.im), z ∈ N' → (⟨z, hz⟩ : ℍ) ∈ N := by
    rintro z hz ⟨x, hx, rfl⟩
    exact hx
  have hstab : ∀ (γ : SL(2, ℤ)) (z : ℂ), 0 < z.im → z ∈ N' → smulC γ z ∈ N' →
      γ • τ₀ = τ₀ := by
    intro γ z hz h1 h2
    refine hNγ γ ⟨z, hz⟩ (hN'mem z hz h1) ?_
    have := hN'mem _ (im_smulC_pos γ hz) h2
    simpa only [smulC_of_im_pos γ hz] using this
  -- a disc on which `F` has fibres the orbits of the stabiliser
  have hcont : Tendsto (cayInv τ) (𝓝 0) (𝓝 τ) := by
    have := (analyticAt_cayInv τ (zero_ne_one (α := ℂ))).continuousAt.tendsto
    rwa [cayInv_zero] at this
  have hev : ∀ᶠ s in 𝓝 (0 : ℂ), ‖s‖ < 1 ∧ cayInv τ s ∈ N' := by
    filter_upwards [ball_mem_nhds (0 : ℂ) one_pos, hcont hN'] with s h1 h2
    exact ⟨by rwa [mem_ball_zero_iff] at h1, h2⟩
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hQ : ∀ s₁ ∈ ball (0 : ℂ) δ₀, ∀ s₂ ∈ ball (0 : ℂ) δ₀, F s₁ = F s₂ →
      ∃ u : ℂ, u ^ e = 1 ∧ s₂ = u * s₁ := by
    intro s₁ h₁ s₂ h₂ hF
    obtain ⟨h₁1, h₁N⟩ := hball s₁ h₁
    obtain ⟨h₂1, h₂N⟩ := hball s₂ h₂
    have hz₁ := im_cayInv_pos hτ h₁1
    have hz₂ := im_cayInv_pos hτ h₂1
    obtain ⟨γ, hγ⟩ := Heights.exists_smul_eq_of_modularJ_eq ⟨_, hz₂⟩ ⟨_, hz₁⟩ (by
      rw [← jC_of_im_pos hz₂, ← jC_of_im_pos hz₁]; exact hF.symm)
    have hsm : smulC γ (cayInv τ s₁) = cayInv τ s₂ := by rw [smulC_of_im_pos γ hz₁, hγ]
    have hfix : γ • τ₀ = τ₀ := hstab γ _ hz₁ h₁N (by rw [hsm]; exact h₂N)
    refine ⟨cmul γ τ₀, hS γ hfix, ?_⟩
    have := cay_smulC hfix hz₁
    rwa [hsm, cay_cayInv hτ h₂1, cay_cayInv hτ h₁1] at this
  have hRF : ∀ s ∈ ball (0 : ℂ) δ₀, F (cmul γ₀ τ₀ * s) = F s := by
    intro s hs
    obtain ⟨h1, -⟩ := hball s hs
    have hz := im_cayInv_pos hτ h1
    have h2 := cay_smulC hγ₀ hz
    rw [cay_cayInv hτ h1] at h2
    have h3 : cayInv τ (cmul γ₀ τ₀ * s) = smulC γ₀ (cayInv τ s) := by
      rw [← h2, cayInv_cay hτ (im_smulC_pos γ₀ hz)]
    simp only [F]
    rw [h3, jC_smulC γ₀ hz]
  have hj : AnalyticAt ℂ jC τ := differentiableOn_jC.analyticAt (isOpen_upper.mem_nhds hτ)
  have hFan : AnalyticAt ℂ F 0 :=
    (by rw [cayInv_zero]; exact hj : AnalyticAt ℂ jC (cayInv τ 0)).comp
      (analyticAt_cayInv τ (zero_ne_one (α := ℂ)))
  obtain ⟨φ, hφ, hφ0, hφ', hFφ⟩ := exists_localForm_of_rot hFan hδ₀ hQ hR hRF
  have hF0 : F 0 = w := by simp only [F, cayInv_zero, w]
  -- Choose a centered ball in the coordinate neighborhood and a disc whose inverse lies in it.
  have hevφ : ∀ᶠ s in 𝓝 (0 : ℂ), F s = w + φ s ^ e ∧ AnalyticAt ℂ φ s ∧
      deriv φ s ≠ 0 ∧ s ∈ ball (0 : ℂ) δ₀ := by
    filter_upwards [hFφ, hφ.eventually_analyticAt, hφ.deriv.continuousAt.eventually_ne hφ',
      ball_mem_nhds _ hδ₀] with s h1 h2 h3 h4
    exact ⟨h1.trans (by rw [hF0]), h2, h3, h4⟩
  obtain ⟨δ₁, hδ₁, hballφ⟩ := Metric.eventually_nhds_iff_ball.mp hevφ
  obtain ⟨r₀, hr₀, E, ψ, hE, hEO, h0E, -, hleft, hright, hψ⟩ :=
    exists_chart (φ := φ) (O := ball (0 : ℂ) δ₁) isOpen_ball (mem_ball_self hδ₁)
      (fun s hs ↦ (hballφ s hs).2.1) (fun s hs ↦ (hballφ s hs).2.2.1) hφ0
  obtain ⟨δ, hδ, hδE⟩ := Metric.isOpen_iff.mp hE 0 h0E
  have hψ0 : ψ 0 = 0 := by
    simpa only [hφ0] using hleft 0 h0E
  have hψt : Tendsto ψ (𝓝 0) (𝓝 0) := by
    have ht := (hψ.continuousOn.continuousAt (ball_mem_nhds 0 hr₀)).tendsto
    rwa [hψ0] at ht
  have hevψ : ∀ᶠ t in 𝓝 (0 : ℂ), t ∈ ball 0 r₀ ∧ ψ t ∈ ball 0 δ := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hr₀, hψt (ball_mem_nhds (0 : ℂ) hδ)]
      with t ht hψtδ
    exact ⟨ht, hψtδ⟩
  obtain ⟨r, hr, hrBall⟩ := Metric.eventually_nhds_iff_ball.mp hevψ
  have hsmall {s : ℂ} (hs : s ∈ ball 0 δ) : F s = w + φ s ^ e ∧ s ∈ ball 0 δ₀ := by
    have h := hballφ s (hEO (hδE hs))
    exact ⟨h.1, h.2.2.2⟩
  have hnorm {s : ℂ} (hs : s ∈ ball 0 δ) : ‖s‖ < 1 :=
    (hball s (hsmall hs).2).1
  set U : Set ℂ := upper ∩ cay τ ⁻¹' ball 0 δ ∩ jC ⁻¹' ball w (r ^ e)
  have hmemU : ∀ z ∈ U, 0 < z.im ∧ cay τ z ∈ ball (0 : ℂ) δ ∧
      jC z = w + φ (cay τ z) ^ e ∧ ‖φ (cay τ z)‖ < r := by
    rintro z ⟨⟨hz, hs⟩, hjz⟩
    have hpow : jC z = w + φ (cay τ z) ^ e := by
      rw [← (hsmall hs).1]
      simp only [F, cayInv_cay hτ hz]
    refine ⟨hz, hs, hpow, ?_⟩
    rw [mem_preimage, mem_ball, dist_eq_norm, hpow, add_sub_cancel_left, norm_pow] at hjz
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hr.le he.ne').mp hjz
  refine ⟨r, hr, U, fun z ↦ φ (cay τ z), fun t ↦ cayInv τ (ψ t),
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : IsOpen (upper ∩ cay τ ⁻¹' ball 0 δ) :=
      (continuousOn_cay hτ).isOpen_inter_preimage isOpen_upper isOpen_ball
    exact (continuousOn_jC.mono inter_subset_left).isOpen_inter_preimage h1 isOpen_ball
  · intro z hz
    rw [mem_ball_zero_iff]
    exact (hmemU z hz).2.2.2
  · intro t ht
    obtain ⟨ht₀, hψtδ⟩ := hrBall t ht
    have hz := im_cayInv_pos hτ (hnorm hψtδ)
    refine ⟨⟨hz, ?_⟩, ?_⟩
    · rw [mem_preimage, cay_cayInv hτ (hnorm hψtδ)]
      exact hψtδ
    · have hjt : jC (cayInv τ (ψ t)) = w + t ^ e := by
        change F (ψ t) = w + t ^ e
        rw [(hsmall hψtδ).1, hright t ht₀]
      rw [mem_preimage, hjt, mem_ball, dist_eq_norm, add_sub_cancel_left, norm_pow]
      exact pow_lt_pow_left₀ (mem_ball_zero_iff.mp ht) (norm_nonneg _) he.ne'
  · intro z hz
    obtain ⟨hz', hs, -, -⟩ := hmemU z hz
    change cayInv τ (ψ (φ (cay τ z))) = z
    rw [hleft _ (hδE hs), cayInv_cay hτ hz']
  · intro t ht
    obtain ⟨ht₀, hψtδ⟩ := hrBall t ht
    change φ (cay τ (cayInv τ (ψ t))) = t
    rw [cay_cayInv hτ (hnorm hψtδ), hright t ht₀]
  · intro t ht
    obtain ⟨ht₀, hψtδ⟩ := hrBall t ht
    have hψdiff := (hψ t ht₀).differentiableAt (isOpen_ball.mem_nhds ht₀)
    have hdiff : DifferentiableAt ℂ (cayInv τ) (ψ t) := by
      have hne : ψ t ≠ 1 := by
        intro h
        have hlt := hnorm hψtδ
        rw [h, norm_one] at hlt
        exact lt_irrefl _ hlt
      exact (analyticAt_cayInv τ hne).differentiableAt
    exact (hdiff.comp t hψdiff).differentiableWithinAt
  · intro z hz
    exact (hmemU z hz).2.2.1
  · refine ⟨⟨hτ, ?_⟩, ?_⟩
    · rw [mem_preimage, cay_self]
      exact mem_ball_self hδ
    · rw [mem_preimage, mem_ball, dist_self]
      exact pow_pos hr e
  · exact inter_subset_left.trans inter_subset_left
  · exact (by rw [cay_self]; exact hφ : AnalyticAt ℂ φ (cay τ τ)).comp (analyticAt_cay hτ hτ)
  · rw [cay_self, hφ0]
  · change deriv (φ ∘ cay τ) τ ≠ 0
    rw [deriv_comp _ (by rw [cay_self]; exact hφ.differentiableAt)
      (analyticAt_cay hτ hτ).differentiableAt, cay_self]
    exact mul_ne_zero hφ' (deriv_cay_ne_zero hτ)
  · intro γ z hz hγz
    obtain ⟨hz', hs, -, -⟩ := hmemU z hz
    obtain ⟨hγz', hγs, -, -⟩ := hmemU _ hγz
    have h1 := (hball _ (hsmall hs).2).2
    have h2 := (hball _ (hsmall hγs).2).2
    rw [cayInv_cay hτ hz'] at h1
    rw [cayInv_cay hτ hγz'] at h2
    exact smulC_eq_self_iff.mpr (hstab γ z hz' h1 h2)
  · intro γ hγ z hz
    have hfix := smulC_eq_self_iff.mp hγ
    obtain ⟨⟨hz', hs⟩, hjz⟩ := hz
    refine ⟨⟨im_smulC_pos γ hz', ?_⟩, ?_⟩
    · rw [mem_preimage, cay_smulC hfix hz', mem_ball_zero_iff, norm_mul, norm_cmul, one_mul,
        ← mem_ball_zero_iff]
      exact hs
    · rw [mem_preimage, jC_smulC γ hz']
      exact hjz

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi
