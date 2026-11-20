/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/S1/Arith.lean, lines 61–132
-/
import Solutions.Source_ReferenceIutCanLiftHolomorphicInverse
import Solutions.Source_ReferenceIutCanLiftLatticeCover
import Solutions.Source_ReferenceIutCanLiftTakeuchiJOrb
import Solutions.Source_ReferenceIutCanLiftTakeuchiModularMobius
import Solutions.Source_ReferenceIutCanLiftTakeuchiOrbifoldLift
import Mathlib.Topology.Homotopy.Lifting

set_option autoImplicit false

open AbcAdaptation.Reference.Heights (modularJ)
open Complex Filter Function Set Topology
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi

/-- The lift of the orbifold pullback through modular `j` is a real Möbius map. -/
theorem exists_mobius_lift_of_orbifold (hL : OrbLiftStatement) (hJ : JOrbStatement)
    {L : PeriodPair} (U : LatticeComplementCover L) {F : ℂ → ℂ}
    (hFo : IsOrbCover F (L.lattice : Set ℂ)ᶜ sig)
    (hFl : ∀ u ∉ L.lattice, HasLocalForm F u (sig (F u))) :
    ∃ m : SL(2, ℝ), ∀ τ : ℍ, modularJ (m • τ) = F (U.ψ τ) := by
  let Ψ : ℂ → ℂ := F ∘ U.Ψ
  have hΨloc : ∀ z ∈ upper, HasLocalForm Ψ z (sig (Ψ z)) := fun z hz ↦
    HasLocalForm.comp (hFl _ (U.notMem z hz))
      (U.differentiableOn.analyticAt (isOpen_upper.mem_nhds hz)) (U.deriv_ne_zero z hz)
  have hΨd : DifferentiableOn ℂ Ψ upper := fun z hz ↦
    (hΨloc z hz).analyticAt.differentiableAt.differentiableWithinAt
  obtain ⟨h₀, hh₀d, hh₀m, hh₀⟩ := hL jC Ψ upper sig sig_pos hJ.1 hΨd hΨloc
  obtain ⟨k₁, hk₁d, hk₁m, hk₁⟩ := hL F jC _ sig sig_pos hFo differentiableOn_jC hJ.2
  have hk₁c : Continuous fun τ : ℍ ↦ k₁ τ :=
    hk₁d.continuousOn.comp_continuous continuous_coe fun τ ↦ τ.im_pos
  obtain ⟨z₀, hz₀⟩ := U.surj (k₁ UpperHalfPlane.I) (hk₁m (UpperHalfPlane.I).im_pos)
  obtain ⟨kC, ⟨-, hkC⟩, -⟩ := U.covering.existsUnique_continuousMap_lifts
    (⟨fun τ : ℍ ↦ k₁ τ, hk₁c⟩ : C(ℍ, ℂ)) (a₀ := UpperHalfPlane.I) (e₀ := z₀) hz₀
    fun τ ↦ hk₁m τ.im_pos
  let k : ℍ → ℍ := kC
  have hkψ : ∀ τ, U.Ψ (k τ) = k₁ τ := fun τ ↦ congrFun hkC τ
  have hkH : HolomorphicH k := by
    intro z hz
    have hkd : HasStrictDerivAt U.Ψ (deriv U.Ψ (k (ofComplex z))) (k (ofComplex z)) :=
      (U.differentiableOn.analyticAt (isOpen_upper.mem_nhds (k (ofComplex z)).im_pos)).hasStrictDerivAt
    refine (HolomorphicInverse.differentiableAt_of_comp_eq (f := U.Ψ) (g := k₁)
      (σ := fun w ↦ (k (ofComplex w) : ℂ)) hkd (U.holo (k (ofComplex z))).2
      ?_ ?_ (hk₁d.differentiableAt (isOpen_upper.mem_nhds hz))).differentiableWithinAt
    · exact (continuous_coe.comp kC.continuous).continuousAt.comp
        (ofComplex.continuousOn.continuousAt (ofComplex.open_source.mem_nhds (by
          change z ∈ (isOpenEmbedding_coe.toOpenPartialHomeomorph _).target
          simp only [IsOpenEmbedding.toOpenPartialHomeomorph_target]
          exact ⟨(⟨z, hz⟩ : ℍ), rfl⟩)))
    · filter_upwards [isOpen_upper.mem_nhds hz] with w hw
      rw [hkψ, ofComplex_of_im_pos hw]
  let h : ℍ → ℍ := fun τ ↦ ⟨h₀ τ, hh₀m τ.im_pos⟩
  have hhH : HolomorphicH h :=
    hh₀d.congr fun z hz ↦ congrArg h₀ (ofComplex_of_im_pos hz)
  have hjh : ∀ τ, modularJ (h τ) = Ψ τ := fun τ ↦ by
    rw [← jC_coe]
    exact hh₀ τ τ.im_pos
  have hHj : ∀ τ, modularJ ((h ∘ k) τ) = modularJ τ := fun τ ↦ by
    rw [Function.comp_apply, hjh, ← jC_coe τ]
    change F (U.Ψ (k τ)) = jC τ
    rw [hkψ]
    exact hk₁ τ τ.im_pos
  obtain ⟨δ, hδ⟩ := exists_SL2Z_eq_of_modularJ (holomorphicH_comp hhH hkH) hHj
  obtain ⟨g, hg⟩ := exists_SL2R_eq_of_leftInverse (S := fun τ ↦ (toSLR δ)⁻¹ • h τ) hkH
    (hhH.smul _) fun τ ↦ by
      change (toSLR δ)⁻¹ • (h ∘ k) τ = τ
      rw [hδ τ, inv_smul_smul]
  let m : SL(2, ℝ) := toSLR δ * g⁻¹
  have hm : ∀ τ, h τ = m • τ := fun τ ↦ by
    have hCompose := hδ (g⁻¹ • τ)
    rw [Function.comp_apply, hg, smul_inv_smul] at hCompose
    rw [hCompose, mul_smul]
  exact ⟨m, fun τ ↦ (congrArg modularJ (hm τ).symm).trans (hjh τ)⟩

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi
