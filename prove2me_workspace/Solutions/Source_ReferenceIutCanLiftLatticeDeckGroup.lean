/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original path Oka/Uniformization/DeckGroup.lean
-/
import Solutions.Source_ReferenceIutCanLiftDeckGroup
import Solutions.Source_ReferenceIutCanLiftHolomorphicInverse
import Solutions.Source_ReferenceIutCanLiftLatticeCover
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Topology.Homotopy.Lifting

set_option autoImplicit false

open Complex Filter Set Topology
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.LatticeComplementCover

variable {L : PeriodPair} (U : LatticeComplementCover L)

private theorem add_notMem {z l : ℂ} (hz : z ∉ L.lattice) (hl : l ∈ L.lattice) :
    z + l ∉ L.lattice :=
  fun h ↦ hz (by simpa using sub_mem h hl)

/-- Two continuous lifts agreeing at a point of the upper half-plane agree everywhere. -/
theorem eq_of_comp_eq {T S : ℍ → ℍ} (hT : Continuous T) (hS : Continuous S)
    (h : ∀ τ, U.ψ (T τ) = U.ψ (S τ)) {τ₀ : ℍ} (h₀ : T τ₀ = S τ₀) : T = S := by
  obtain ⟨F, -, hF⟩ :=
    U.covering.existsUnique_continuousMap_lifts ⟨fun τ ↦ U.ψ (T τ), U.continuous_ψ.comp hT⟩
      (a₀ := τ₀) (e₀ := T τ₀) rfl fun τ ↦ U.ψ_notMem (T τ)
  have h₁ := hF ⟨T, hT⟩ ⟨rfl, rfl⟩
  have h₂ := hF ⟨S, hS⟩ ⟨h₀.symm, by funext τ; exact (h τ).symm⟩
  exact congrArg (fun G : C(ℍ, ℍ) ↦ (G : ℍ → ℍ)) (h₁.trans h₂.symm)

/-- Translation by a period lifts through the covering of the lattice complement. -/
theorem exists_lift {l : ℂ} (hl : l ∈ L.lattice) (τ τ' : ℍ)
    (h : U.ψ τ' = U.ψ τ + l) :
    ∃ T : ℍ → ℍ, Continuous T ∧ T τ = τ' ∧ ∀ σ, U.ψ (T σ) = U.ψ σ + l := by
  obtain ⟨F, ⟨hF₀, hF⟩, -⟩ :=
    U.covering.existsUnique_continuousMap_lifts ⟨fun σ ↦ U.ψ σ + l,
      U.continuous_ψ.add continuous_const⟩ (a₀ := τ) (e₀ := τ') h
      fun σ ↦ add_notMem (U.ψ_notMem σ) hl
  exact ⟨F, F.continuous, hF₀, fun σ ↦ congrFun hF σ⟩

/-- A continuous lift of a period translation is holomorphic on the upper half-plane. -/
theorem holomorphicH_of_lift {T : ℍ → ℍ} (hT : Continuous T) {l : ℂ}
    (h : ∀ σ, U.ψ (T σ) = U.ψ σ + l) : HolomorphicH T := by
  intro z hz
  have hd : HasStrictDerivAt U.Ψ (deriv U.Ψ (T (ofComplex z))) (T (ofComplex z)) :=
    (U.differentiableOn.analyticAt (isOpen_upper.mem_nhds (T (ofComplex z)).im_pos)).hasStrictDerivAt
  refine (HolomorphicInverse.differentiableAt_of_comp_eq
    (f := U.Ψ) (g := fun w ↦ U.Ψ w + l) hd (U.holo (T (ofComplex z))).2
    ?_ ?_ ?_).differentiableWithinAt
  · refine (continuous_coe.comp hT).continuousAt.comp
      (ofComplex.continuousOn.continuousAt (ofComplex.open_source.mem_nhds ?_))
    change z ∈ (isOpenEmbedding_coe.toOpenPartialHomeomorph _).target
    simp only [IsOpenEmbedding.toOpenPartialHomeomorph_target]
    exact ⟨(⟨z, hz⟩ : ℍ), rfl⟩
  · filter_upwards [isOpen_upper.mem_nhds hz] with w hw
    have hw' := h (ofComplex w)
    simp only [ψ] at hw'
    rw [hw', ofComplex_of_im_pos hw]
  · exact (U.holo ⟨z, hz⟩).1.add_const l

/-- The deck group for the map to the lattice complement modulo the lattice. -/
def deckGroup : Subgroup SL(2, ℝ) where
  carrier := {g | ∃ l ∈ L.lattice, ∀ τ, U.ψ (g • τ) = U.ψ τ + l}
  one_mem' := ⟨0, zero_mem _, fun τ ↦ by simp⟩
  mul_mem' := by
    rintro g g' ⟨l, hl, hg⟩ ⟨m, hm, hg'⟩
    exact ⟨m + l, add_mem hm hl, fun τ ↦ by rw [mul_smul, hg, hg', add_assoc]⟩
  inv_mem' := by
    rintro g ⟨l, hl, hg⟩
    refine ⟨-l, neg_mem hl, fun τ ↦ ?_⟩
    have heq := hg (g⁻¹ • τ)
    rw [smul_inv_smul] at heq
    rw [heq]
    ring

theorem mem_deckGroup {g : SL(2, ℝ)} :
    g ∈ U.deckGroup ↔ ∃ l ∈ L.lattice, ∀ τ, U.ψ (g • τ) = U.ψ τ + l :=
  Iff.rfl

theorem neg_one_mem_deckGroup : (-1 : SL(2, ℝ)) ∈ U.deckGroup :=
  ⟨0, zero_mem _, fun τ ↦ by rw [neg_one_act, add_zero]⟩

theorem smul_mem_iff {g : SL(2, ℝ)} (hg : g ∈ U.deckGroup) (τ : ℍ) :
    U.ψ (g • τ) - U.ψ τ ∈ L.lattice := by
  obtain ⟨l, hl, h⟩ := hg
  rw [h]
  simpa using hl

/-- Deck transformations act transitively on fibers modulo the lattice. -/
theorem exists_mem_deckGroup {τ τ' : ℍ} (h : U.ψ τ' - U.ψ τ ∈ L.lattice) :
    ∃ g ∈ U.deckGroup, g • τ = τ' := by
  let l := U.ψ τ' - U.ψ τ
  have hl : l ∈ L.lattice := h
  obtain ⟨T, hTc, hTτ, hT⟩ := U.exists_lift hl τ τ' (by dsimp [l]; ring)
  obtain ⟨S, hSc, hSτ, hS⟩ := U.exists_lift (neg_mem hl) τ' τ (by dsimp [l]; ring)
  have hTS : T ∘ S = id := U.eq_of_comp_eq (hTc.comp hSc) continuous_id
    (fun σ ↦ by simp [hT, hS, add_assoc]) (τ₀ := τ') (by simp [hSτ, hTτ])
  have hST : S ∘ T = id := U.eq_of_comp_eq (hSc.comp hTc) continuous_id
    (fun σ ↦ by simp [hT, hS, add_assoc]) (τ₀ := τ) (by simp [hSτ, hTτ])
  obtain ⟨g, hg⟩ := exists_SL2R_eq_of_holomorphic (U.holomorphicH_of_lift hTc hT)
    (U.holomorphicH_of_lift hSc hS) (fun σ ↦ congrFun hTS σ) (fun σ ↦ congrFun hST σ)
  exact ⟨g, ⟨l, hl, fun σ ↦ (congrArg U.ψ (hg σ).symm).trans (hT σ)⟩,
    (hg τ).symm.trans hTτ⟩

theorem sub_mem_lattice_iff {τ τ' : ℍ} :
    U.ψ τ' - U.ψ τ ∈ L.lattice ↔ ∃ g ∈ U.deckGroup, g • τ = τ' := by
  constructor
  · exact U.exists_mem_deckGroup
  · rintro ⟨g, hg, rfl⟩
    exact U.smul_mem_iff hg τ

/-- A deck transformation that fixes one point acts trivially on the upper half-plane. -/
theorem smul_eq_self_of_fixed {g : SL(2, ℝ)} (hg : g ∈ U.deckGroup) {τ : ℍ}
    (hτ : g • τ = τ) : ∀ σ : ℍ, g • σ = σ := by
  obtain ⟨l, _, h⟩ := hg
  have hl : l = 0 := by
    have heq := h τ
    rw [hτ] at heq
    linear_combination -heq
  exact congrFun (U.eq_of_comp_eq (T := fun σ : ℍ ↦ g • σ) (S := id)
    (continuous_const_smul g) continuous_id (fun σ ↦ by simp [h, hl]) hτ)

theorem eq_one_or_neg_one {g : SL(2, ℝ)} (hg : g ∈ U.deckGroup) {τ : ℍ}
    (hτ : g • τ = τ) : g = 1 ∨ g = -1 :=
  eq_one_or_neg_one_of_forall (U.smul_eq_self_of_fixed hg hτ)

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.LatticeComplementCover
