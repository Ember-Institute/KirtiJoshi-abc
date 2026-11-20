/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original paths OrbicurveCores/S1/Defs.lean, lines 45–63, and
OrbicurveCores/S1/EllOrb.lean, lines 31–102.
-/
import Solutions.Source_ReferenceIutCanLiftTakeuchiOrbifoldLocalForm
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.ByContra

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi

open Complex Metric Set Filter Function Bornology
open scoped Topology

/-- An orbifold chart of `p` over the disc `ball w (ρ ^ n)`: `u` maps the open set `U` bijectively
onto `ball 0 ρ`, with holomorphic inverse `v`, and `p = w + u ^ n` on `U`. -/
structure OrbChart (p : ℂ → ℂ) (w : ℂ) (n : ℕ) (ρ : ℝ) (U : Set ℂ) (u v : ℂ → ℂ) : Prop where
  isOpen : IsOpen U
  mapsTo_u : MapsTo u U (ball 0 ρ)
  mapsTo_v : MapsTo v (ball 0 ρ) U
  v_u : ∀ y ∈ U, v (u y) = y
  u_v : ∀ t ∈ ball (0 : ℂ) ρ, u (v t) = t
  differentiableOn_v : DifferentiableOn ℂ v (ball 0 ρ)
  eq_pow : ∀ y ∈ U, p y = w + u y ^ n

/-- `p : Y → ℂ` is an **orbifold covering** of `ℂ` with signature `e`: every value is attained on
`Y`, and for every `w` there is `ρ > 0` such that the part of `Y` over `ball w (ρ ^ e w)` is a
disjoint union of orbifold charts. -/
def IsOrbCover (p : ℂ → ℂ) (Y : Set ℂ) (e : ℂ → ℕ) : Prop :=
  ∀ w : ℂ, (∃ y ∈ Y, p y = w) ∧ ∃ ρ > (0 : ℝ), ∃ (ι : Type) (U : ι → Set ℂ) (u v : ι → ℂ → ℂ),
    Pairwise (Disjoint on U) ∧ (∀ i, U i ⊆ Y ∧ OrbChart p w (e w) ρ (U i) (u i) (v i)) ∧
      ∀ y ∈ Y, p y ∈ ball w (ρ ^ e w) → ∃ i, y ∈ U i

/-- The upper half-plane as a subset of `ℂ`. -/
abbrev upper : Set ℂ := {z : ℂ | 0 < z.im}

/-- **Inverse function theorem, chart form.** A function `φ` analytic with nonvanishing derivative
on an open set `O ∋ u₀`, `φ u₀ = 0`, maps an open `E ⊆ O` containing `u₀` injectively (with left
inverse `ψ`) and has a holomorphic section `ψ` over a disc `ball 0 ρ₀` with values in `E`. -/
theorem exists_chart {φ : ℂ → ℂ} {O : Set ℂ} {u₀ : ℂ} (hO : IsOpen O) (hu₀ : u₀ ∈ O)
    (han : ∀ y ∈ O, AnalyticAt ℂ φ y) (hd : ∀ y ∈ O, deriv φ y ≠ 0) (h0 : φ u₀ = 0) :
    ∃ ρ₀ > (0 : ℝ), ∃ (E : Set ℂ) (ψ : ℂ → ℂ), IsOpen E ∧ E ⊆ O ∧ u₀ ∈ E ∧
      MapsTo ψ (ball 0 ρ₀) E ∧ (∀ y ∈ E, ψ (φ y) = y) ∧ (∀ t ∈ ball (0 : ℂ) ρ₀, φ (ψ t) = t) ∧
      DifferentiableOn ℂ ψ (ball 0 ρ₀) := by
  have hs : HasStrictDerivAt φ (deriv φ u₀) u₀ := (han u₀ hu₀).hasStrictDerivAt
  have hs' := hs.hasStrictFDerivAt_equiv (hd u₀ hu₀)
  set e := hs'.toOpenPartialHomeomorph φ
  have he : ∀ y, e y = φ y := fun y ↦ rfl
  have hsrc : u₀ ∈ e.source := hs'.mem_toOpenPartialHomeomorph_source
  have hT : IsOpen (e.target ∩ e.symm ⁻¹' O) :=
    e.continuousOn_symm.isOpen_inter_preimage e.open_target hO
  have h1 : e u₀ = 0 := by rw [he, h0]
  have h0T : (0 : ℂ) ∈ e.target ∩ e.symm ⁻¹' O := by
    refine ⟨h1 ▸ e.map_source hsrc, ?_⟩
    rw [mem_preimage, ← h1, e.left_inv hsrc]; exact hu₀
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.mp hT 0 h0T
  refine ⟨ρ₀, hρ₀, e.source ∩ O, e.symm, e.open_source.inter hO, inter_subset_right,
    ⟨hsrc, hu₀⟩, fun t ht ↦ ⟨e.map_target (hball ht).1, (hball ht).2⟩,
    fun y hy ↦ e.left_inv hy.1, fun t ht ↦ e.right_inv (hball ht).1, ?_⟩
  intro t ht
  have htT := hball ht
  have hO' : e.symm t ∈ O := htT.2
  have hsymm := e.hasStrictDerivAt_symm htT.1 (hd _ hO') (han _ hO').hasStrictDerivAt
  exact (HasStrictDerivAt.hasDerivAt hsymm).differentiableAt.differentiableWithinAt

/-- Neighborhoods of a fiber contain the inverse image of a small disc about its value if
`G` is continuous off its poles and tends to infinity at its poles and at infinity. -/
theorem exists_dist_lt_imp_mem {G : ℂ → ℂ} {Z M : Set ℂ} {w : ℂ} (hM : IsOpen M)
    (hcont : ContinuousOn G Zᶜ) (hfib : ∀ x ∉ Z, G x = w → x ∈ M)
    (hpole : ∀ z ∈ Z, Tendsto G (𝓝[≠] z) (cobounded ℂ))
    (hinf : Tendsto G (cobounded ℂ) (cobounded ℂ)) :
    ∃ δ > (0 : ℝ), ∀ x ∉ Z, dist (G x) w < δ → x ∈ M := by
  by_contra! hcon
  set l := comap G (𝓝 w) ⊓ 𝓟 (Zᶜ ∩ Mᶜ)
  haveI hl : l.NeBot := by
    refine ((nhds_basis_ball.comap G).inf_principal _).neBot_iff.mpr ?_
    intro δ hδ
    obtain ⟨x, hxZ, hxd, hxM⟩ := hcon δ hδ
    exact ⟨x, hxd, hxZ, hxM⟩
  have hGl : Tendsto G l (𝓝 w) := tendsto_comap.mono_left inf_le_left
  have hb : IsBounded (G ⁻¹' ball w 1) := by
    rw [isBounded_def, ← preimage_compl]
    exact hinf (isBounded_def.mp isBounded_ball)
  have hK : IsCompact (closure (G ⁻¹' ball w 1)) :=
    isCompact_of_isClosed_isBounded isClosed_closure hb.closure
  have hlK : l ≤ 𝓟 (closure (G ⁻¹' ball w 1)) := by
    rw [le_principal_iff]
    exact mem_of_superset (hGl (ball_mem_nhds w one_pos)) subset_closure
  obtain ⟨x, -, hx⟩ := hK hlK
  haveI : (𝓝 x ⊓ l).NeBot := hx
  have hZM : Zᶜ ∩ Mᶜ ∈ 𝓝 x ⊓ l := mem_inf_of_right (mem_inf_of_right (mem_principal_self _))
  by_cases hxZ : x ∈ Z
  · have hle : 𝓝 x ⊓ l ≤ 𝓝[≠] x := by
      refine le_inf inf_le_left (le_principal_iff.mpr (mem_of_superset hZM ?_))
      rintro y ⟨hy, -⟩ rfl
      exact hy hxZ
    exact ((hpole x hxZ).mono_left hle).not_tendsto (disjoint_cobounded_nhds w)
      (hGl.mono_left inf_le_right)
  · have hle : 𝓝 x ⊓ l ≤ 𝓝[Zᶜ] x :=
      le_inf inf_le_left (le_principal_iff.mpr (mem_of_superset hZM inter_subset_left))
    have hGx : G x = w :=
      tendsto_nhds_unique ((hcont x hxZ).tendsto.mono_left hle) (hGl.mono_left inf_le_right)
    have hMx : M ∩ (Zᶜ ∩ Mᶜ) ∈ 𝓝 x ⊓ l :=
      inter_mem (mem_inf_of_left (hM.mem_nhds (hfib x hxZ hGx))) hZM
    obtain ⟨y, hy1, -, hy2⟩ := Filter.nonempty_of_mem hMx
    exact hy2 hy1

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi
