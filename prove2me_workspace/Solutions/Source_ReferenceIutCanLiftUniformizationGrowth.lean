/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the upstream files.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original paths Oka/Uniformization/{Integrality,OncePunctured,R3,Uniqueness}.lean
-/
import Solutions.Source_ReferenceIutCanLiftInvariantPolynomialGenerator
import Solutions.Source_ReferenceIutCanLiftLatticeComplement
import Solutions.Source_ReferenceIutCanLiftLatticeDepthGrowth
import Solutions.Source_ReferenceIutCanLiftLatticeGenerators
import Solutions.Source_ReferenceIutCanLiftLatticeUniformization
import Solutions.Source_ReferenceIutCanLiftUniformizationUnique
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

open Polynomial UpperHalfPlane WeierstrassCurve
open scoped MatrixGroups Pointwise

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

open AbcAdaptation.Reference.Heights

private theorem conjugate_mem_commensurator {G : Type*} [Group G]
    {P Q : Subgroup G} {g n : G}
    (hgroups : ∀ γ : G, γ ∈ Q ↔ g * γ * g⁻¹ ∈ P)
    (hn : n ∈ Subgroup.Commensurable.commensurator Q) :
    g * n * g⁻¹ ∈ Subgroup.Commensurable.commensurator P := by
  have hP : ConjAct.toConjAct g • Q = P := by
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
      ConjAct.toConjAct_inv_smul, hgroups]
    rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
  have hmul : ConjAct.toConjAct (g * n * g⁻¹) * ConjAct.toConjAct g =
      ConjAct.toConjAct g * ConjAct.toConjAct n := by
    simpa only [ConjAct.toConjAct_mul] using
      congrArg (ConjAct.toConjAct : G → ConjAct G)
        (show (g * n * g⁻¹) * g = g * n by group)
  rw [Subgroup.Commensurable.commensurator_mem_iff] at hn ⊢
  rw [← hP, ← mul_smul, hmul, mul_smul]
  exact hn.conj (ConjAct.toConjAct g)

private theorem polyBdd_vcX_smul {F : ℍ → ℂ} (C : VariableChange ℂ) {n : SL(2, ℝ)}
    (hb : PolyBdd F fun τ ↦ ‖F (n • τ)‖) :
    PolyBdd (fun τ ↦ vcX C (F τ)) fun τ ↦ ‖vcX C (F (n • τ))‖ := by
  let x : ℍ → ℂ := fun τ ↦ vcX C (F τ)
  let scale := ‖(C.u : ℂ) ^ 2‖
  let offset := ‖C.r‖
  let baseScale := 1 + scale + offset
  have hscale : 0 ≤ scale := norm_nonneg _
  have hoffset : 0 ≤ offset := norm_nonneg _
  have hbase (τ : ℍ) : 2 + ‖F τ‖ ≤ baseScale * (2 + ‖x τ‖) := by
    have hcoord : F τ = (C.u : ℂ) ^ 2 * x τ + C.r :=
      vcX_injective C (vcX_of C (x τ)).symm
    have hnorm : ‖F τ‖ ≤ scale * ‖x τ‖ + offset := by
      calc
        ‖F τ‖ = ‖(C.u : ℂ) ^ 2 * x τ + C.r‖ := congrArg norm hcoord
        _ ≤ ‖(C.u : ℂ) ^ 2 * x τ‖ + ‖C.r‖ := norm_add_le _ _
        _ = scale * ‖x τ‖ + offset := by rw [norm_mul]
    dsimp only [baseScale]
    nlinarith only [hscale, hoffset, hnorm, norm_nonneg (x τ),
      mul_nonneg hoffset (norm_nonneg (x τ))]
  have hgrowth : PolyBdd x (fun τ ↦ ‖F (n • τ)‖) := by
    obtain ⟨K, N, hK⟩ := hb
    refine ⟨|K| * baseScale ^ N, N, fun τ ↦ ?_⟩
    calc
      ‖F (n • τ)‖ ≤ K * (2 + ‖F τ‖) ^ N := hK τ
      _ ≤ |K| * (baseScale * (2 + ‖x τ‖)) ^ N :=
        mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (by positivity) (hbase τ) N)
          (by positivity) (abs_nonneg _)
      _ = (|K| * baseScale ^ N) * (2 + ‖x τ‖) ^ N := by rw [mul_pow, mul_assoc]
  have hsum : PolyBdd x (fun τ ↦ ‖F (n • τ)‖ + offset) :=
    hgrowth.add (PolyBdd.const offset)
  have hscaled : PolyBdd x (fun τ ↦ (‖F (n • τ)‖ + offset) * scale⁻¹) :=
    hsum.mul (PolyBdd.const scale⁻¹) (fun _ ↦ add_nonneg (norm_nonneg _) hoffset)
      (fun _ ↦ inv_nonneg.mpr hscale)
  refine hscaled.mono fun τ ↦ ?_
  change ‖vcX C (F (n • τ))‖ ≤ (‖F (n • τ)‖ + offset) * scale⁻¹
  rw [vcX, norm_div, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (inv_nonneg.mpr hscale)

namespace IsUniformization

variable {W : WeierstrassCurve ℂ} [W.IsElliptic] {A B : SL(2, ℝ)} {π : ℂ → ℂ × ℂ}

/-- In any uniformization of a once-punctured elliptic curve, the first coordinate
has polynomial growth under precomposition by a commensurator element. -/
theorem polyBdd_fst_smul_of_commensurator (h : IsUniformization W A B π)
    {n : SL(2, ℝ)}
    (hn : n ∈ Subgroup.Commensurable.commensurator (Subgroup.closure {A, B})) :
    PolyBdd (fun τ : ℍ ↦ (π τ).1) fun τ ↦ ‖(π (n • τ : ℍ)).1‖ := by
  obtain ⟨t, C, hC⟩ := exists_variableChange_latticeCurve W
  let U := latticeComplementCover (periodPair t)
  let π₀ := latticeParameterization t C ∘ U.Ψ
  have hdeck := Generators.deckGroup_eq_pmGroup U
  have h₀ : IsUniformization W (Generators.A U) (Generators.B U) π₀ := by
    rw [← hC]
    exact U.uniformizes C hdeck
  obtain ⟨g, hg, hΓ⟩ := h₀.unique h
  have hcomm : Subgroup.Commensurable (Subgroup.closure {A, B}) (pmGroup A B) := by
    refine ⟨relIndex_closure_pmGroup_ne_zero A B, ?_⟩
    rw [Subgroup.relIndex_eq_one.mpr (closure_le_pmGroup A B)]
    exact one_ne_zero
  have hn' : n ∈ Subgroup.Commensurable.commensurator (pmGroup A B) := by
    rwa [← hcomm.eq]
  have hconj : g * n * g⁻¹ ∈ Subgroup.Commensurable.commensurator U.deckGroup := by
    rw [hdeck]
    exact conjugate_mem_commensurator hΓ hn'
  have hb :
      PolyBdd (fun τ : ℍ ↦ (π₀ τ).1) fun τ ↦ ‖(π₀ ((g * n * g⁻¹) • τ : ℍ)).1‖ := by
    simpa only [π₀, Function.comp_apply, latticeParameterization, Peripheral.wpΨ,
      LatticeComplementCover.ψ] using
      (polyBdd_vcX_smul C (Peripheral.exists_poly_bound_smul hconj))
  obtain ⟨K, N, hK⟩ := hb
  refine ⟨K, N, fun τ ↦ ?_⟩
  have hsmul : (g * n * g⁻¹) • (g • τ) = g • (n • τ) := by
    rw [← mul_smul, show (g * n * g⁻¹) * g = g * n by group, mul_smul]
  change ‖(π (n • τ : ℍ)).1‖ ≤ K * (2 + ‖(π τ).1‖) ^ N
  rw [hg τ, hg (n • τ)]
  simpa only [hsmul] using hK (g • τ)

/-- Finite relative index supplies an invariant polynomial whose fibers are the
commensurator orbits of the given uniformization. -/
theorem exists_invariant_polynomial_generator_of_finite_commensurator_index
    (h : IsUniformization W A B π)
    (hfin : (Subgroup.closure {A, B}).relIndex
      (Subgroup.Commensurable.commensurator (Subgroup.closure {A, B})) ≠ 0) :
    ∃ s : ℂ[X], 0 < s.natDegree ∧
      (∀ n ∈ Subgroup.Commensurable.commensurator (Subgroup.closure {A, B}),
        ∀ τ : ℍ, s.eval (π (n • τ : ℍ)).1 = s.eval (π τ).1) ∧
      ∀ τ τ' : ℍ, s.eval (π τ).1 = s.eval (π τ').1 →
        ∃ n ∈ Subgroup.Commensurable.commensurator (Subgroup.closure {A, B}), n • τ = τ' :=
  h.exists_invariant_polynomial_generator_for_commensurator hfin
    (fun _ hn ↦ h.polyBdd_fst_smul_of_commensurator hn)

end IsUniformization

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
