/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the upstream files.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Source: Oka/Uniformization/Uniqueness.lean at
75dcdc3faadd10b986afb9283e89902bcdddecd4 of https://github.com/lana-agents/oka.
-/
import Solutions.Source_ReferenceIutCanLiftDeckGroup
import Mathlib.Tactic.Group
import Mathlib.Topology.Homotopy.Lifting

set_option autoImplicit false

open UpperHalfPlane hiding I
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.IsUniformization

variable {W : WeierstrassCurve ℂ} {A B A' B' : SL(2, ℝ)} {π π' : ℂ → ℂ × ℂ}

/-- Uniformizations of the same affine elliptic curve differ by an upper half-plane
automorphism, which also conjugates their deck groups. -/
theorem unique [W.IsElliptic] (h : IsUniformization W A B π)
    (h' : IsUniformization W A' B' π') :
    ∃ g : SL(2, ℝ), (∀ z : ℍ, π' z = π ((g • z : ℍ) : ℂ)) ∧
      ∀ γ : SL(2, ℝ), γ ∈ pmGroup A' B' ↔ g * γ * g⁻¹ ∈ pmGroup A B := by
  have hcov := h.isCoveringMap
  have hcov' := h'.isCoveringMap
  let x₀ := h'.toV UpperHalfPlane.I
  obtain ⟨z₀, hz₀⟩ := h.surj x₀.1.1 x₀.1.2 x₀.2
  have hz₀' : h.toV z₀ = x₀ := Subtype.ext hz₀
  obtain ⟨T, ⟨hT0, hT⟩, -⟩ := hcov.existsUnique_continuousMap_lifts
    ⟨h'.toV, h'.continuous_toV⟩ UpperHalfPlane.I z₀ hz₀'
  obtain ⟨S, ⟨hS0, hS⟩, -⟩ := hcov'.existsUnique_continuousMap_lifts
    ⟨h.toV, h.continuous_toV⟩ z₀ UpperHalfPlane.I hz₀'.symm
  have hT' (z : ℍ) : h.toV (T z) = h'.toV z := congrFun hT z
  have hS' (z : ℍ) : h'.toV (S z) = h.toV z := congrFun hS z
  have hTS : Function.LeftInverse T S := by
    refine congrFun (hcov.eq_of_comp_eq (A := ℍ)
      (g₁ := fun z ↦ T (S z)) (g₂ := id) (T.continuous.comp S.continuous) continuous_id
      ?_ z₀ ?_)
    · funext z
      exact (hT' (S z)).trans (hS' z)
    · change T (S z₀) = z₀
      rw [hS0, hT0]
  have hST : Function.LeftInverse S T := by
    refine congrFun (hcov'.eq_of_comp_eq (A := ℍ)
      (g₁ := fun z ↦ S (T z)) (g₂ := id) (S.continuous.comp T.continuous) continuous_id
      ?_ UpperHalfPlane.I ?_)
    · funext z
      exact (hS' (T z)).trans (hT' z)
    · change S (T UpperHalfPlane.I) = UpperHalfPlane.I
      rw [hT0, hS0]
  have hπT (z : ℍ) : π (T z) = π' z := congrArg Subtype.val (hT' z)
  have hπS (z : ℍ) : π' (S z) = π z := congrArg Subtype.val (hS' z)
  obtain ⟨g, hg⟩ := exists_SL2R_eq_of_holomorphic
    (h.holomorphicH_of_lift (fun z ↦ (h'.holo z).1) T.continuous hπT)
    (h'.holomorphicH_of_lift (fun z ↦ (h.holo z).1) S.continuous hπS) hTS hST
  have hgT (z : ℍ) : h.toV (g • z) = h'.toV z := by rw [← hg, hT']
  refine ⟨g, fun z ↦ (congrArg Subtype.val (hgT z)).symm, fun γ ↦ ⟨?_, ?_⟩⟩
  · intro hγ
    refine h.mem_pmGroup_of_deck fun z ↦ ?_
    rw [mul_smul, mul_smul, hgT, h'.toV_smul_pm hγ, ← hgT, smul_inv_smul]
  · intro hγ
    refine h'.mem_pmGroup_of_deck fun z ↦ ?_
    rw [← hgT (γ • z), ← hgT z, ← mul_smul,
      show g * γ = (g * γ * g⁻¹) * g by group, mul_smul, h.toV_smul_pm hγ]

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.IsUniformization
