/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original paths OrbicurveCores/S1/Rigidity/Lattice.lean and OrbicurveCores/S1/Rigidity/Lift.lean
-/
import Solutions.Source_ReferenceIutCanLiftLatticeComplement
import Solutions.Source_ReferenceIutCanLiftLatticeGenerators
import Solutions.Source_ReferenceIutCanLiftLatticeUniformization
import Solutions.Source_ReferenceIutCanLiftSL2Facts
import Solutions.Source_ReferenceIutCanLiftUniformizationUnique
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

open UpperHalfPlane hiding I
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi.Rigidity

open AbcAdaptation.Reference.Heights WeierstrassCurve

/-- A holomorphic lift through the period lattice that meets every nonzero lattice class. -/
structure IsLatticeLift (τ : ℍ) (σ : ℂ → ℂ) : Prop where
  notMem : ∀ z : ℂ, 0 < z.im → σ z ∉ (periodPair τ).lattice
  differentiableAt : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ σ z
  deriv_ne_zero : ∀ z : ℂ, 0 < z.im → deriv σ z ≠ 0
  exists_sub_mem : ∀ x ∉ (periodPair τ).lattice,
    ∃ z : ℂ, 0 < z.im ∧ σ z - x ∈ (periodPair τ).lattice

private noncomputable def mob (g : SL(2, ℝ)) (z : ℂ) : ℂ :=
  ((g 0 0 : ℂ) * z + g 0 1) / ((g 1 0 : ℂ) * z + g 1 1)

private theorem hasDerivAt_mob (g : SL(2, ℝ)) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (mob g) (((g 1 0 : ℂ) * z + g 1 1) ^ 2)⁻¹ z := by
  have h₁ : HasDerivAt (fun v : ℂ ↦ (g 0 0 : ℂ) * v + g 0 1) (g 0 0 : ℂ) z := by
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id z).const_mul (g 0 0 : ℂ)).add_const (g 0 1 : ℂ))
  have h₂ : HasDerivAt (fun v : ℂ ↦ (g 1 0 : ℂ) * v + g 1 1) (g 1 0 : ℂ) z := by
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id z).const_mul (g 1 0 : ℂ)).add_const (g 1 1 : ℂ))
  have hdet : (g 0 0 : ℂ) * g 1 1 - (g 0 1 : ℂ) * g 1 0 = 1 := by
    exact_mod_cast det_SL g
  unfold mob
  refine (h₁.fun_div h₂ (denom_SL2R_ne_zero g hz)).congr_deriv ?_
  rw [← one_div, show (g 0 0 : ℂ) * ((g 1 0 : ℂ) * z + g 1 1) -
      ((g 0 0 : ℂ) * z + g 0 1) * (g 1 0 : ℂ) = 1 by linear_combination hdet]

/-- A given uniformization lifts to a period-lattice complement. Its fibers modulo the lattice
are the orbits of the given matrix pair. -/
theorem exists_isLatticeLift {W : WeierstrassCurve ℂ} [W.IsElliptic]
    {A B : SL(2, ℝ)} {π : ℂ → ℂ × ℂ} (h : IsUniformization W A B π) :
    ∃ τ : ℍ, W.j = modularJ τ ∧ ∃ σ : ℂ → ℂ, IsLatticeLift τ σ ∧
      ∀ z w : ℍ, σ z - σ w ∈ (periodPair τ).lattice ↔
        ∃ γ ∈ Subgroup.closure {A, B}, γ • z = w := by
  obtain ⟨τ, C, rfl⟩ := exists_variableChange_latticeCurve W
  letI : (latticeCurve τ).IsElliptic := latticeCurve_isElliptic τ
  let U := latticeComplementCover (periodPair τ)
  have hCanonical := U.uniformizes C (Generators.deckGroup_eq_pmGroup U)
  obtain ⟨g, hg, -⟩ := hCanonical.unique h
  let σ : ℂ → ℂ := U.Ψ ∘ mob g
  have hMob (z : ℍ) : mob g z = ((g • z : ℍ) : ℂ) := (coe_SL2R_smul g z).symm
  have hσ (z : ℍ) : σ z = U.Ψ (g • z : ℍ) := congrArg U.Ψ (hMob z)
  have hNotMem (z : ℍ) : σ z ∉ (periodPair τ).lattice := by
    rw [hσ z]
    exact U.notMem _ (g • z).im_pos
  have hHolo (z : ℍ) : DifferentiableAt ℂ σ (z : ℂ) ∧ deriv σ (z : ℂ) ≠ 0 := by
    have hU := U.holo (g • z)
    rw [← hMob z] at hU
    have hDeriv := hU.1.hasDerivAt.comp (z : ℂ) (hasDerivAt_mob g z.im_pos)
    refine ⟨hDeriv.differentiableAt, ?_⟩
    change deriv (U.Ψ ∘ mob g) (z : ℂ) ≠ 0
    rw [hDeriv.deriv]
    exact mul_ne_zero hU.2 (inv_ne_zero (pow_ne_zero _ (denom_SL2R_ne_zero g z.im_pos)))
  refine ⟨τ, (variableChange_j (latticeCurve τ) C).trans (latticeCurve_j_eq_modularJ τ),
    σ, ⟨fun z hz ↦ hNotMem ⟨z, hz⟩, fun z hz ↦ (hHolo ⟨z, hz⟩).1,
      fun z hz ↦ (hHolo ⟨z, hz⟩).2, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨w, hw⟩ := U.surj x hx
    let z := g⁻¹ • w
    have hz : σ z = x := by
      rw [hσ z, show g • z = w from smul_inv_smul g w]
      exact hw
    exact ⟨z, z.im_pos, by rw [hz, sub_self]; exact zero_mem _⟩
  · intro z w
    have hParam (v : ℍ) : latticeParameterization τ C (σ v) = π v := by
      simpa only [hσ v, Function.comp_apply] using (hg v).symm
    rw [← latticeParameterization_eq_iff τ C (hNotMem z) (hNotMem w), hParam z, hParam w]
    exact h.fibre z w

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi.Rigidity
