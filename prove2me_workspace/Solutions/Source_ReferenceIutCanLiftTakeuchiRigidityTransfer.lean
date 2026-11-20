/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/S1/Rigidity/Transfer.lean, lines 26–219
Also uses the quotient topology and compactness from Heights/LatticeQuotientTopology.lean
and Heights/LatticeQuotientCompact.lean at 721496ca4c158e511d25d8ccf6bfe8503eda73c1.
-/
import Solutions.Source_ReferenceIutCanLiftTakeuchiRigidityLift
import Solutions.Source_ReferenceIutCanLiftConvexCoveringLift
import Solutions.Source_ReferenceIutCanLiftHolomorphicInverse
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Covering.Quotient

set_option autoImplicit false

open Complex Filter Function Metric Set Topology
open UpperHalfPlane hiding I

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi.Rigidity

open AbcAdaptation.Reference.Heights

/-- The projection onto the quotient of `ℂ` by the period lattice. -/
noncomputable abbrev quotientMk (τ : ℍ) : ℂ → LatticeQuotient τ :=
  QuotientAddGroup.mk' (periodPair τ).lattice.toAddSubgroup

theorem isDiscrete_lattice (τ : ℍ) : IsDiscrete ((periodPair τ).lattice : Set ℂ) :=
  isDiscrete_iff_discreteTopology.mpr (inferInstanceAs (DiscreteTopology (periodPair τ).lattice))

theorem quotientMk_eq_iff (τ : ℍ) {a b : ℂ} :
    quotientMk τ a = quotientMk τ b ↔ a - b ∈ (periodPair τ).lattice :=
  QuotientAddGroup.eq_iff_sub_mem

private theorem quotientMk_zero (τ : ℍ) : quotientMk τ 0 = 0 := map_zero (QuotientAddGroup.mk' _)

theorem quotientMk_eq_zero_iff (τ : ℍ) {a : ℂ} :
    quotientMk τ a = 0 ↔ a ∈ (periodPair τ).lattice := by
  rw [← quotientMk_zero τ, quotientMk_eq_iff, sub_zero]

private theorem continuous_quotientMk (τ : ℍ) :
    Continuous (quotientMk τ) := QuotientAddGroup.continuous_mk

private theorem nhds_quotientMk (τ : ℍ) (z : ℂ) :
    𝓝 (quotientMk τ z) = Filter.map (quotientMk τ) (𝓝 z) :=
  QuotientAddGroup.nhds_eq (periodPair τ).lattice.toAddSubgroup z

private theorem isCoveringMap_quotientMk (τ : ℍ) : IsCoveringMap (quotientMk τ) :=
  (AddSubgroup.isAddQuotientCoveringMap_of_comm (periodPair τ).lattice.toAddSubgroup
    (isDiscrete_lattice τ)).isCoveringMap

private theorem compactSpace_latticeQuotient (τ : ℍ) : CompactSpace (LatticeQuotient τ) := by
  apply isCompact_univ_iff.mp
  rw [← (QuotientAddGroup.mk'_surjective (periodPair τ).lattice.toAddSubgroup).range_eq]
  exact IsZLattice.isCompact_range_of_periodic (periodPair τ).lattice (quotientMk τ)
    (continuous_quotientMk τ) (fun z w hw ↦ (quotientMk_eq_iff τ).mpr (by simpa using hw))

variable {τ τ' : ℍ} {σ σ' : ℂ → ℂ}

private theorem IsLatticeLift.hasStrictDerivAt (hσ : IsLatticeLift τ σ) {z : ℂ} (hz : 0 < z.im) :
    HasStrictDerivAt σ (deriv σ z) z :=
  ((show DifferentiableOn ℂ σ {w | 0 < w.im} from
      fun w hw ↦ (hσ.differentiableAt w hw).differentiableWithinAt).analyticAt
    (isOpen_upper.mem_nhds hz)).hasStrictDerivAt

private theorem IsLatticeLift.continuousOn (hσ : IsLatticeLift τ σ) :
    ContinuousOn σ {z : ℂ | 0 < z.im} :=
  fun z hz ↦ (hσ.differentiableAt z hz).continuousAt.continuousWithinAt

/-- Local holomorphic sections of `σ` modulo `Λ` near every point of `ℂ ∖ Λ`. -/
private theorem IsLatticeLift.exists_chart (hσ : IsLatticeLift τ σ) {x₀ : ℂ}
    (hx₀ : x₀ ∉ (periodPair τ).lattice) :
    ∃ δ > 0, ∃ s : ℂ → ℂ, ContinuousOn s (ball x₀ δ) ∧ ∀ y ∈ ball x₀ δ,
      0 < (s y).im ∧ σ (s y) - y ∈ (periodPair τ).lattice ∧ DifferentiableAt ℂ s y := by
  obtain ⟨z₀, hz₀, hl⟩ := hσ.exists_sub_mem x₀ hx₀
  obtain ⟨ε, hε, s₀, hs₀c, hs₀, hs₀z⟩ :=
    HolomorphicInverse.exists_localSection (hσ.hasStrictDerivAt hz₀) (hσ.deriv_ne_zero z₀ hz₀)
  have hup : s₀ ⁻¹' {z : ℂ | 0 < z.im} ∈ 𝓝 (σ z₀) :=
    (hs₀c.continuousAt (ball_mem_nhds _ hε)).preimage_mem_nhds
      (by rw [hs₀z]; exact isOpen_upper.mem_nhds hz₀)
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.mem_nhds_iff.mp hup
  have hmap : ∀ y ∈ ball x₀ (min ε δ₁), y + (σ z₀ - x₀) ∈ ball (σ z₀) (min ε δ₁) := by
    intro y hy
    rw [mem_ball, dist_eq_norm] at hy ⊢
    rwa [show y + (σ z₀ - x₀) - σ z₀ = y - x₀ by ring]
  have hsub : ball (σ z₀) (min ε δ₁) ⊆ ball (σ z₀) ε := ball_subset_ball (min_le_left _ _)
  refine ⟨min ε δ₁, lt_min hε hδ₁, fun y ↦ s₀ (y + (σ z₀ - x₀)), ?_, fun y hy ↦ ?_⟩
  · exact hs₀c.comp (continuousOn_id.add continuousOn_const) fun y hy ↦ hsub (hmap y hy)
  · have hw := hmap y hy
    have hwε := hsub hw
    have him : 0 < (s₀ (y + (σ z₀ - x₀))).im :=
      hball (ball_subset_ball (min_le_right _ _) hw)
    refine ⟨him, ?_, ?_⟩
    · rw [hs₀ _ hwε, show y + (σ z₀ - x₀) - y = σ z₀ - x₀ by ring]
      exact hl
    · have hd : DifferentiableAt ℂ s₀ (y + (σ z₀ - x₀)) :=
        HolomorphicInverse.differentiableAt_of_comp_eq (hσ.hasStrictDerivAt him)
          (hσ.deriv_ne_zero _ him) (hs₀c.continuousAt (isOpen_ball.mem_nhds hwε))
          (g := id) (by
            filter_upwards [isOpen_ball.mem_nhds hwε] with v hv
            exact hs₀ v hv) differentiableAt_id
      exact hd.comp y (differentiableAt_id.add_const _)

/-- `σ` and `σ'` have the same fibres modulo their lattices. -/
def SameFibres (τ τ' : ℍ) (σ σ' : ℂ → ℂ) : Prop :=
  ∀ z w : ℂ, 0 < z.im → 0 < w.im →
    (σ z - σ w ∈ (periodPair τ).lattice ↔ σ' z - σ' w ∈ (periodPair τ').lattice)

lemma SameFibres.symm (h : SameFibres τ τ' σ σ') : SameFibres τ' τ σ' σ :=
  fun z w hz hw ↦ (h z w hz hw).symm

/-- The induced map `ℂ / Λ → ℂ / Λ'`, `σ z ↦ σ' z`, `0 ↦ 0`. -/
noncomputable def transfer (τ τ' : ℍ) (σ σ' : ℂ → ℂ) (q : LatticeQuotient τ) :
    LatticeQuotient τ' := by
  classical
  exact if h : ∃ z : ℂ, 0 < z.im ∧ quotientMk τ (σ z) = q then quotientMk τ' (σ' h.choose) else 0

private theorem transfer_mk_apply (hrel : SameFibres τ τ' σ σ') {z : ℂ} (hz : 0 < z.im) :
    transfer τ τ' σ σ' (quotientMk τ (σ z)) = quotientMk τ' (σ' z) := by
  have h : ∃ w : ℂ, 0 < w.im ∧ quotientMk τ (σ w) = quotientMk τ (σ z) := ⟨z, hz, rfl⟩
  rw [transfer, dif_pos h, quotientMk_eq_iff]
  obtain ⟨hw, hwz⟩ := h.choose_spec
  exact (hrel _ _ hw hz).mp ((quotientMk_eq_iff τ).mp hwz)

lemma transfer_mk_of_mem (hσ : IsLatticeLift τ σ) {x : ℂ} (hx : x ∈ (periodPair τ).lattice) :
    transfer τ τ' σ σ' (quotientMk τ x) = 0 := by
  rw [transfer, dif_neg]
  rintro ⟨z, hz, h⟩
  rw [(quotientMk_eq_zero_iff τ).mpr hx, quotientMk_eq_zero_iff] at h
  exact hσ.notMem z hz h

lemma transfer_transfer (hσ : IsLatticeLift τ σ) (hσ' : IsLatticeLift τ' σ')
    (hrel : SameFibres τ τ' σ σ') (q : LatticeQuotient τ) :
    transfer τ' τ σ' σ (transfer τ τ' σ σ' q) = q := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
  change transfer τ' τ σ' σ (transfer τ τ' σ σ' (quotientMk τ x)) = quotientMk τ x
  by_cases hx : x ∈ (periodPair τ).lattice
  · rw [transfer_mk_of_mem hσ hx, ← quotientMk_zero τ', transfer_mk_of_mem hσ' (zero_mem _),
      (quotientMk_eq_zero_iff τ).mpr hx]
  · obtain ⟨z, hz, hzx⟩ := hσ.exists_sub_mem x hx
    rw [← (quotientMk_eq_iff τ).mpr hzx, transfer_mk_apply hrel hz, transfer_mk_apply hrel.symm hz]

private theorem continuousAt_transfer_mk (hσ : IsLatticeLift τ σ) (hσ' : IsLatticeLift τ' σ')
    (hrel : SameFibres τ τ' σ σ') {x₀ : ℂ} (hx₀ : x₀ ∉ (periodPair τ).lattice) :
    ContinuousAt (transfer τ τ' σ σ') (quotientMk τ x₀) := by
  obtain ⟨δ, hδ, s, hsc, hs⟩ := hσ.exists_chart hx₀
  have heq : (fun y ↦ quotientMk τ' (σ' (s y))) =ᶠ[𝓝 x₀] transfer τ τ' σ σ' ∘ quotientMk τ := by
    filter_upwards [ball_mem_nhds x₀ hδ] with y hy
    obtain ⟨him, hmem, -⟩ := hs y hy
    rw [comp_apply, ← (quotientMk_eq_iff τ).mpr hmem, transfer_mk_apply hrel him]
  have hc : ContinuousAt (fun y ↦ quotientMk τ' (σ' (s y))) x₀ :=
    (continuous_quotientMk τ').continuousAt.comp
      ((hσ'.differentiableAt _ (hs x₀ (mem_ball_self hδ)).1).continuousAt.comp
        (hsc.continuousAt (ball_mem_nhds x₀ hδ)))
  rw [ContinuousAt, nhds_quotientMk, tendsto_map'_iff]
  exact hc.congr heq

/-- If the inverse of a bijection is continuous away from `f x₀`, then `f` is continuous at `x₀`.
The source must be Hausdorff and the target must be compact. -/
private theorem continuousAt_of_inverse {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [CompactSpace Y] {f : X → Y} {g : Y → X} (hgf : ∀ x, g (f x) = x)
    (hfg : ∀ y, f (g y) = y) {x₀ : X} (hg : ∀ y, y ≠ f x₀ → ContinuousAt g y) :
    ContinuousAt f x₀ := by
  rw [ContinuousAt, _root_.tendsto_nhds]
  intro N hN hx₀N
  have hK : IsCompact Nᶜ := hN.isClosed_compl.isCompact
  have hgK : IsCompact (g '' Nᶜ) := hK.image_of_continuousOn fun y hy ↦
    (hg y fun h ↦ hy (h ▸ hx₀N)).continuousWithinAt
  have hx₀K : x₀ ∉ g '' Nᶜ := by
    rintro ⟨y, hy, hyx⟩
    exact hy (by rw [← hfg y, hyx]; exact hx₀N)
  filter_upwards [hgK.isClosed.isOpen_compl.mem_nhds hx₀K] with x hx
  by_contra hfx
  exact hx ⟨f x, hfx, hgf x⟩

private theorem continuous_transfer (hσ : IsLatticeLift τ σ) (hσ' : IsLatticeLift τ' σ')
    (hrel : SameFibres τ τ' σ σ') : Continuous (transfer τ τ' σ σ') := by
  letI : T1Space (LatticeQuotient τ) :=
    QuotientAddGroup.t1Space_iff.mpr (periodPair τ).isClosed_lattice
  letI : CompactSpace (LatticeQuotient τ') := compactSpace_latticeQuotient τ'
  rw [continuous_iff_continuousAt]
  intro q
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
  change ContinuousAt _ (quotientMk τ x)
  by_cases hx : x ∈ (periodPair τ).lattice
  · refine continuousAt_of_inverse (transfer_transfer hσ hσ' hrel)
      (transfer_transfer hσ' hσ hrel.symm) fun y hy ↦ ?_
    obtain ⟨x', rfl⟩ := QuotientAddGroup.mk'_surjective _ y
    have hx' : x' ∉ (periodPair τ').lattice := fun h ↦ hy (by
      change quotientMk τ' x' = _
      rw [transfer_mk_of_mem hσ hx, (quotientMk_eq_zero_iff τ').mpr h])
    exact continuousAt_transfer_mk hσ' hσ hrel.symm hx'
  · exact continuousAt_transfer_mk hσ hσ' hrel hx

/-- The map of lattice quotients lifts to an entire function on `ℂ` that fixes zero. -/
theorem exists_entire_lift (hσ : IsLatticeLift τ σ) (hσ' : IsLatticeLift τ' σ')
    (hrel : SameFibres τ τ' σ σ') :
    ∃ β : ℂ → ℂ, Differentiable ℂ β ∧ β 0 = 0 ∧
      ∀ x, quotientMk τ' (β x) = transfer τ τ' σ σ' (quotientMk τ x) := by
  have hT := continuous_transfer hσ hσ' hrel
  obtain ⟨β, hβc, hβ, hβ0⟩ := (isCoveringMap_quotientMk τ').isCoveringMapOn
    |>.exists_lift_of_convex convex_univ
      (hT.comp (continuous_quotientMk τ)).continuousOn (mapsTo_univ _ _)
      (a₀ := 0) (mem_univ _) (e₀ := 0)
      ((quotientMk_zero τ').trans (transfer_mk_of_mem hσ (zero_mem _)).symm)
  have hβc' : Continuous β := continuousOn_univ.mp hβc
  have hβ' (x : ℂ) : quotientMk τ' (β x) = transfer τ τ' σ σ' (quotientMk τ x) :=
    hβ x (mem_univ _)
  -- Away from the lattice, a local section identifies β up to a period.
  have hdiff : ∀ x₀ ∉ (periodPair τ).lattice, DifferentiableAt ℂ β x₀ := by
    intro x₀ hx₀
    obtain ⟨δ, hδ, s, hsc, hs⟩ := hσ.exists_chart hx₀
    have hFc : ContinuousOn (fun y ↦ β y - σ' (s y)) (ball x₀ δ) :=
      hβc'.continuousOn.sub (hσ'.continuousOn.comp hsc fun y hy ↦ (hs y hy).1)
    have hFm : MapsTo (fun y ↦ β y - σ' (s y)) (ball x₀ δ) (periodPair τ').lattice := by
      intro y hy
      obtain ⟨him, hmem, -⟩ := hs y hy
      change β y - σ' (s y) ∈ (periodPair τ').lattice
      rw [← quotientMk_eq_iff, hβ', ← (quotientMk_eq_iff τ).mpr hmem,
        transfer_mk_apply hrel him]
    have heq : (fun y ↦ σ' (s y) + (β x₀ - σ' (s x₀))) =ᶠ[𝓝 x₀] β := by
      filter_upwards [ball_mem_nhds x₀ hδ] with y hy
      have := (isPreconnected_ball).constant_of_mapsTo (isDiscrete_lattice τ') hFc hFm hy
        (mem_ball_self hδ)
      rw [← this]
      ring
    obtain ⟨him, -, hsd⟩ := hs x₀ (mem_ball_self hδ)
    exact (((hσ'.differentiableAt _ him).comp x₀ hsd).add_const _).congr_of_eventuallyEq
      heq.symm
  -- Continuity makes the singularities at the lattice points removable.
  have hβd : Differentiable ℂ β := by
    intro c
    by_cases hc : c ∈ (periodPair τ).lattice
    · have hS := (periodPair τ).compl_lattice_sdiff_singleton_mem_nhds c
      have : DifferentiableOn ℂ β ((↑(periodPair τ).lattice \ {c})ᶜ) := by
        refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff hS).mp
          ⟨fun y hy ↦ (hdiff y fun h ↦ hy.1 ⟨h, hy.2⟩).differentiableWithinAt,
            hβc'.continuousAt⟩
      exact this.differentiableAt hS
    · exact hdiff c hc
  exact ⟨β, hβd, hβ0, hβ'⟩

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi.Rigidity
