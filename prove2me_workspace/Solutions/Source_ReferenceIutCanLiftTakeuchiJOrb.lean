/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original paths OrbicurveCores/S1/Defs.lean, lines 74–78, and
OrbicurveCores/S1/JOrb.lean, lines 784–950.
-/
import Solutions.Source_ReferenceIutCanLiftTakeuchiJLocalCharts
import Solutions.Source_ReferenceIutCanLiftTakeuchiModularStabilizers
import Mathlib.Analysis.Complex.Polynomial.Basic

set_option autoImplicit false

open AbcAdaptation.Reference
open Complex Filter Function Metric Set Topology
open UpperHalfPlane hiding I
open scoped MatrixGroups Topology UpperHalfPlane

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi

/-- Modular `j` has the orbifold charts and local normal forms with signature `sig`. -/
def JOrbStatement : Prop :=
  IsOrbCover jC upper sig ∧ ∀ z ∈ upper, HasLocalForm jC z (sig (jC z))

/-! ### Translates of the charts -/

theorem image_smulC_eq {U : Set ℂ} (hU : U ⊆ upper) (γ : SL(2, ℤ)) :
    smulC γ '' U = upper ∩ smulC γ⁻¹ ⁻¹' U := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨im_smulC_pos γ (hU hz), by rw [mem_preimage, smulC_inv_smulC γ (hU hz)]; exact hz⟩
  · rintro ⟨hy, hy'⟩
    exact ⟨_, hy', smulC_smulC_inv γ hy⟩

variable {τ₀ : ℂ} {e : ℕ} {r : ℝ} {U : Set ℂ} {u v : ℂ → ℂ}

theorem JChartData.translate (hD : JChartData τ₀ e r U u v) (γ : SL(2, ℤ)) :
    smulC γ '' U ⊆ upper ∧ OrbChart jC (jC τ₀) e r (smulC γ '' U)
      (fun z ↦ u (smulC γ⁻¹ z)) (fun t ↦ smulC γ (v t)) := by
  have hsub := hD.sub
  have hC := hD.chart
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact im_smulC_pos γ (hsub hz)
  · rw [image_smulC_eq hsub]
    exact (continuousOn_smulC γ⁻¹).isOpen_inter_preimage isOpen_upper hC.isOpen
  · rintro _ ⟨z, hz, rfl⟩
    change u (smulC γ⁻¹ (smulC γ z)) ∈ ball 0 r
    rw [smulC_inv_smulC γ (hsub hz)]
    exact hC.mapsTo_u hz
  · intro t ht
    exact ⟨v t, hC.mapsTo_v ht, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    rw [smulC_inv_smulC γ (hsub hz), hC.v_u z hz]
  · intro t ht
    rw [smulC_inv_smulC γ (hsub (hC.mapsTo_v ht)), hC.u_v t ht]
  · exact (differentiableOn_smulC γ).comp hC.differentiableOn_v
      (fun t ht ↦ hsub (hC.mapsTo_v ht))
  · rintro _ ⟨z, hz, rfl⟩
    rw [smulC_inv_smulC γ (hsub hz), jC_smulC γ (hsub hz), hC.eq_pow z hz]

theorem JChartData.image_stab (hD : JChartData τ₀ e r U u v) {σ : SL(2, ℤ)}
    (hσ : smulC σ τ₀ = τ₀) : smulC σ '' U = U := by
  have hσ' : smulC σ⁻¹ τ₀ = τ₀ := by
    have := smulC_inv_smulC σ (hD.sub hD.mem)
    rwa [hσ] at this
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact hD.inv σ hσ z hz
  · intro z hz
    exact ⟨_, hD.inv σ⁻¹ hσ' z hz, smulC_smulC_inv σ (hD.sub hz)⟩

theorem JChartData.translate_eq (hD : JChartData τ₀ e r U u v) {γ γ' : SL(2, ℤ)}
    (h : ¬ Disjoint (smulC γ '' U) (smulC γ' '' U)) : smulC γ '' U = smulC γ' '' U := by
  obtain ⟨_, ⟨z, hz, rfl⟩, ⟨z', hz', hzz⟩⟩ := not_disjoint_iff.mp h
  have h1 : smulC (γ'⁻¹ * γ) z = z' := by
    rw [← smulC_smulC _ _ (hD.sub hz), ← hzz, smulC_inv_smulC _ (hD.sub hz')]
  have hσ : smulC (γ'⁻¹ * γ) τ₀ = τ₀ := hD.stab _ z hz (by rw [h1]; exact hz')
  have e1 : smulC (γ' * (γ'⁻¹ * γ)) '' U = smulC γ' '' (smulC (γ'⁻¹ * γ) '' U) := by
    rw [image_image]
    exact image_congr fun x hx ↦ (smulC_smulC _ _ (hD.sub hx)).symm
  rw [mul_inv_cancel_left] at e1
  rw [e1, hD.image_stab hσ]

theorem JChartData.cover (hD : JChartData τ₀ e r U u v) (he : 0 < e) (hr : 0 < r) :
    ∃ ρ > (0 : ℝ), ∃ (ι : Type) (U' : ι → Set ℂ) (u' v' : ι → ℂ → ℂ),
      Pairwise (Disjoint on U') ∧
      (∀ i, U' i ⊆ upper ∧ OrbChart jC (jC τ₀) e ρ (U' i) (u' i) (v' i)) ∧
      ∀ y ∈ upper, jC y ∈ ball (jC τ₀) (ρ ^ e) → ∃ i, y ∈ U' i := by
  let ι := {V : Set ℂ // ∃ γ : SL(2, ℤ), V = smulC γ '' U}
  let g : ι → SL(2, ℤ) := fun i ↦ i.2.choose
  have hg : ∀ i : ι, i.1 = smulC (g i) '' U := fun i ↦ i.2.choose_spec
  refine ⟨r, hr, ι, fun i ↦ i.1, fun i z ↦ u (smulC (g i)⁻¹ z),
    fun i t ↦ smulC (g i) (v t), ?_, ?_, ?_⟩
  · intro i j hij
    by_contra h
    apply hij
    apply Subtype.ext
    change ¬ Disjoint i.1 j.1 at h
    rw [hg i, hg j] at h ⊢
    exact hD.translate_eq h
  · intro i
    change i.1 ⊆ upper ∧ OrbChart jC (jC τ₀) e r i.1 (fun z ↦ u (smulC (g i)⁻¹ z))
      (fun t ↦ smulC (g i) (v t))
    rw [hg i]
    exact hD.translate (g i)
  · intro y hy hjy
    rw [mem_ball, dist_eq_norm] at hjy
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (jC y - jC τ₀) he
    have htr : t ∈ ball (0 : ℂ) r := by
      rw [mem_ball_zero_iff]
      rw [← ht, norm_pow] at hjy
      exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hr.le he.ne').mp hjy
    have hz := hD.chart.mapsTo_v htr
    have hz1 := hD.sub hz
    have hjz : jC (v t) = jC y := by
      rw [hD.chart.eq_pow _ hz, hD.chart.u_v t htr, ht]
      ring
    obtain ⟨γ, hγ⟩ := Heights.exists_smul_eq_of_modularJ_eq ⟨y, hy⟩ ⟨v t, hz1⟩ (by
      rw [← jC_of_im_pos hy, ← jC_of_im_pos hz1, hjz])
    refine ⟨⟨smulC γ '' U, γ, rfl⟩, v t, hz, ?_⟩
    rw [smulC_of_im_pos γ hz1, hγ]

theorem JChartData.hasLocalForm (hD : JChartData τ₀ e r U u v) {z : ℂ} (hz : 0 < z.im)
    (hjz : jC z = jC τ₀) : HasLocalForm jC z e := by
  have hτ := hD.sub hD.mem
  obtain ⟨γ, hγ⟩ := Heights.exists_smul_eq_of_modularJ_eq ⟨z, hz⟩ ⟨τ₀, hτ⟩ (by
    rw [← jC_of_im_pos hz, ← jC_of_im_pos hτ, hjz])
  have hγz : smulC γ τ₀ = z := by rw [smulC_of_im_pos γ hτ, hγ]
  have hinv : smulC γ⁻¹ z = τ₀ := by rw [← hγz, smulC_inv_smulC γ hτ]
  obtain ⟨-, hC⟩ := hD.translate γ
  have hu : AnalyticAt ℂ u (smulC γ⁻¹ z) := by rw [hinv]; exact hD.analyticAt
  refine ⟨fun y ↦ u (smulC γ⁻¹ y), hu.comp (analyticAt_smulC γ⁻¹ hz), ?_, ?_, ?_⟩
  · change u (smulC γ⁻¹ z) = 0
    rw [hinv, hD.u_self]
  · change deriv (u ∘ smulC γ⁻¹) z ≠ 0
    rw [deriv_comp _ hu.differentiableAt (analyticAt_smulC γ⁻¹ hz).differentiableAt, hinv]
    exact mul_ne_zero hD.deriv_ne (deriv_smulC_ne_zero γ⁻¹ hz)
  · have hmem : z ∈ smulC γ '' U := ⟨τ₀, hD.mem, hγz⟩
    filter_upwards [hC.isOpen.mem_nhds hmem] with y hy
    rw [hC.eq_pow y hy, hjz]

/-! ### The main theorem -/

theorem exists_jChartData_sig (w : ℂ) :
    ∃ τ₀ : ℍ, jC τ₀ = w ∧ ∃ r > 0, ∃ U u v, JChartData (τ₀ : ℂ) (sig w) r U u v := by
  by_cases h0 : w = 0
  · subst h0
    refine ⟨ρ, jC_ρ, ?_⟩
    have : sig 0 = 3 := if_pos rfl
    rw [this]
    exact exists_jChartData ρ (by norm_num) (fun γ hγ ↦ cmul_cube_of_fix_ρ hγ) gρ_smul
      (fun m hm ↦ dvd_of_ρ_pow (by rwa [cmul_gρ] at hm))
  by_cases h1 : w = 1728
  · subst h1
    refine ⟨UpperHalfPlane.I, jC_I, ?_⟩
    have : sig 1728 = 2 := by simp [sig]
    rw [this]
    exact exists_jChartData _ (by norm_num) (fun γ hγ ↦ cmul_sq_of_fix_I hγ) S_smul_I
      (fun m hm ↦ dvd_of_neg_one_pow (by rwa [cmul_S_I] at hm))
  obtain ⟨τ₀, hτ₀⟩ := Heights.modularJ_surjective w
  refine ⟨τ₀, by rw [jC_coe, hτ₀], ?_⟩
  have : sig w = 1 := by simp [sig, h0, h1]
  rw [this]
  refine exists_jChartData τ₀ one_pos (fun γ hγ ↦ ?_) (one_smul _ τ₀) (fun m _ ↦ one_dvd m)
  have hB : Heights.modularJ τ₀ ∉ jBranch := by
    rw [hτ₀, jBranch_eq]
    simp [h0, h1]
  by_cases g1 : γ = 1
  · subst g1
    simp [cmul]
  by_cases g2 : γ = -1
  · subst g2
    simp [cmul]
  exact absurd (modularJ_mem_jBranch_of_smul_eq hγ g1 g2) hB

/-- **The `j`-function is an orbifold covering** of `ℂ` with signature `sig` (ramification `3`
over `0 = j(ρ)`, `2` over `1728 = j(i)`, and `1` elsewhere), with local normal forms of order
`sig (j z)` at every point of `ℍ`. -/
theorem jOrbStatement : JOrbStatement := by
  refine ⟨fun w ↦ ?_, fun z hz ↦ ?_⟩
  · obtain ⟨τ₀, hτ₀, r, hr, U, u, v, hD⟩ := exists_jChartData_sig w
    refine ⟨⟨τ₀, τ₀.im_pos, hτ₀⟩, ?_⟩
    have := hD.cover (sig_pos w) hr
    rwa [hτ₀] at this
  · obtain ⟨τ₀, hτ₀, r, hr, U, u, v, hD⟩ := exists_jChartData_sig (jC z)
    exact hD.hasLocalForm hz hτ₀.symm

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi
