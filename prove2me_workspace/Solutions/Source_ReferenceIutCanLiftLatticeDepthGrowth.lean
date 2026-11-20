/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original paths Oka/Uniformization/Depth.lean and Oka/Uniformization/Integrality.lean
-/
import Solutions.Source_ReferenceIutCanLiftCommensuratorGrowth
import Solutions.Source_ReferenceIutCanLiftLatticeCuspGrowth
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false

open Complex Metric Set
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
namespace Peripheral

open AbcAdaptation.Reference.Heights Generators

variable {t : ℍ} {U : LatticeComplementCover (periodPair t)}

variable (U) in
/-- The Weierstrass first coordinate of the lattice covering. -/
noncomputable def wpΨ (τ : ℍ) : ℂ := (periodPair t).weierstrassP (U.ψ τ)

theorem wpΨ_smul {γ : SL(2, ℝ)} (hγ : γ ∈ U.deckGroup) (τ : ℍ) :
    wpΨ U (γ • τ) = wpΨ U τ := by
  obtain ⟨l, hl, hψ⟩ := hγ
  simp only [wpΨ, hψ τ]
  exact (periodPair t).weierstrassP_add_coe _ ⟨l, hl⟩

/-- The logarithmic size of the first coordinate and the exponential of orbit depth
bound one another on the entire upper half-plane. -/
theorem exists_growth : ∃ A B : ℝ, 0 ≤ A ∧ ∀ τ : ℍ,
    Real.log (1 + ‖wpΨ U τ‖) ≤ A * Real.exp (depth U τ) + B ∧
      Real.exp (depth U τ) ≤ A * Real.log (2 + ‖wpΨ U τ‖) + B := by
  let c := cuspData U
  obtain ⟨ε, hε, hεr, A₁, B₁, hest⟩ := cusp_estimates c
  have hεr₀ : ε ≤ r₀ t := hεr.trans c.r₁_le
  have hKc : IsCompact (Kε t ε) := isCompact_Kε ε
  have hKK : Kε t ε ⊆ K t := Kε_subset hε
  obtain ⟨C₁, hC₁⟩ := hKc.exists_bound_of_continuousOn
    (f := (periodPair t).weierstrassP)
    (((periodPair t).analyticOnNhd_weierstrassP.continuousOn).mono fun _ hk ↦ K_subset t (hKK hk))
  obtain ⟨C₂, hC₂⟩ := hKc.exists_bound_of_continuousOn (f := fun k ↦ dist (sK U k) (e₀ U))
    (continuous_dist.comp_continuousOn (((continuousOn_sK U).mono hKK).prodMk continuousOn_const))
  let A := max A₁ 1
  let B := max B₁ 0 + Real.log (1 + |C₁|) + Real.exp |C₂|
  have hA : A₁ ≤ A := le_max_left _ _
  have hA0 : 0 ≤ A := zero_le_one.trans (le_max_right _ _)
  have hB : B₁ ≤ max B₁ 0 := le_max_left _ _
  have hB0 : 0 ≤ max B₁ 0 := le_max_right _ _
  have hL1 : 0 ≤ Real.log (1 + |C₁|) := Real.log_nonneg (by linarith [abs_nonneg C₁])
  have hE2 : 0 ≤ Real.exp |C₂| := (Real.exp_pos _).le
  refine ⟨A, B, hA0, fun τ ↦ ?_⟩
  have hlog2 : 0 ≤ Real.log (2 + ‖wpΨ U τ‖) :=
    Real.log_nonneg (by linarith [norm_nonneg (wpΨ U τ)])
  have hexpD := Real.exp_pos (depth U τ)
  rcases compact_or_cusp (U := U) hεr₀ τ with ⟨γ, hγ, k, hk, hγτ⟩ | ⟨γ, hγ, w, hw, hw0, hγτ⟩
  · have h℘ : ‖wpΨ U τ‖ ≤ |C₁| := by
      rw [← wpΨ_smul hγ τ, hγτ]
      simp only [wpΨ, ψ_sK U (hKK hk)]
      exact (hC₁ k hk).trans (le_abs_self _)
    have hD : depth U τ ≤ |C₂| := by
      rw [← depth_smul (τ := τ) hγ, hγτ]
      have h₁ := depth_le (U := U) (τ := sK U k) U.deckGroup.one_mem
      rw [one_smul] at h₁
      have h₂ := hC₂ k hk
      rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg] at h₂
      exact h₁.trans (h₂.trans (le_abs_self _))
    constructor
    · have hlog₁ : Real.log (1 + ‖wpΨ U τ‖) ≤ Real.log (1 + |C₁|) :=
        Real.log_le_log (by positivity) (by linarith only [h℘])
      have hAexp : 0 ≤ A * Real.exp (depth U τ) := mul_nonneg hA0 hexpD.le
      dsimp only [B]
      linarith only [hlog₁, hAexp, hB0, hE2]
    · have hEdist : Real.exp (depth U τ) ≤ Real.exp |C₂| := Real.exp_le_exp.mpr hD
      have hAlog : 0 ≤ A * Real.log (2 + ‖wpΨ U τ‖) := mul_nonneg hA0 hlog2
      dsimp only [B]
      linarith only [hEdist, hAlog, hB0, hL1]
  · have hψ : wpΨ U τ = (periodPair t).weierstrassP w := by
      rw [← wpΨ_smul hγ τ, hγτ]
      simp only [wpΨ]
      rw [ψ_Sig U (log_mem_Hr ⟨ball_subset_ball hεr₀ hw, hw0⟩), Complex.exp_log hw0]
    have hD : depth U τ = depth U (Sig U (Complex.log w)) := by
      rw [← depth_smul (τ := τ) hγ, hγτ]
    obtain ⟨h₁, h₂⟩ := hest w hw hw0
    rw [← hψ, ← hD] at h₁ h₂
    constructor
    · have hAexp := mul_le_mul_of_nonneg_right hA hexpD.le
      dsimp only [B]
      linarith only [h₁, hAexp, hB, hL1, hE2]
    · have hAlog := mul_le_mul_of_nonneg_right hA hlog2
      dsimp only [B]
      linarith only [h₂, hAlog, hB, hL1, hE2]

/-- A commensurator translate of the first coordinate has polynomial growth. -/
theorem exists_poly_bound_smul {σ : SL(2, ℝ)}
    (hσ : σ ∈ Subgroup.Commensurable.commensurator U.deckGroup) :
    PolyBdd (wpΨ U) fun τ ↦ ‖wpΨ U (σ • τ)‖ := by
  obtain ⟨A, B, hA, hAB⟩ := exists_growth (U := U)
  exact polyBdd_smul_of_depth_comparison (Γ := U.deckGroup) (o := e₀ U)
    (F := wpΨ U) hA hAB hσ

end Peripheral
end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
