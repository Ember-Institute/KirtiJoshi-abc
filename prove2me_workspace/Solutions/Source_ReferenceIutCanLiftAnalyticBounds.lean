/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original paths Oka/Uniformization/{FEtTransitive,PmDeck}.lean
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

open UpperHalfPlane

/-- Holomorphy on `ℍ`, as a function on `{Im > 0}`. -/
def HolH (g : ℍ → ℂ) : Prop := DifferentiableOn ℂ (fun z ↦ g (ofComplex z)) {z | 0 < z.im}

/-- `u` is bounded by a polynomial in `‖h₀‖`. -/
def PolyBdd (h₀ : ℍ → ℂ) (u : ℍ → ℝ) : Prop := ∃ C : ℝ, ∃ N : ℕ, ∀ τ, u τ ≤ C * (2 + ‖h₀ τ‖) ^ N

namespace PolyBdd

variable {h₀ : ℍ → ℂ}

theorem const (c : ℝ) : PolyBdd h₀ fun _ ↦ c := ⟨c, 0, fun τ ↦ by simp⟩

theorem mono {u v : ℍ → ℝ} (hv : PolyBdd h₀ v) (h : ∀ τ, u τ ≤ v τ) : PolyBdd h₀ u := by
  obtain ⟨C, N, hC⟩ := hv
  exact ⟨C, N, fun τ ↦ (h τ).trans (hC τ)⟩

theorem add {u v : ℍ → ℝ} (hu : PolyBdd h₀ u) (hv : PolyBdd h₀ v) : PolyBdd h₀ (u + v) := by
  obtain ⟨C, N, hC⟩ := hu
  obtain ⟨D, M, hD⟩ := hv
  refine ⟨|C| + |D|, N + M, fun τ ↦ ?_⟩
  have h1 : 1 ≤ 2 + ‖h₀ τ‖ := by linarith [norm_nonneg (h₀ τ)]
  have hN : (2 + ‖h₀ τ‖) ^ N ≤ (2 + ‖h₀ τ‖) ^ (N + M) := pow_le_pow_right₀ h1 (by omega)
  have hM : (2 + ‖h₀ τ‖) ^ M ≤ (2 + ‖h₀ τ‖) ^ (N + M) := pow_le_pow_right₀ h1 (by omega)
  have hp : 0 ≤ (2 + ‖h₀ τ‖) ^ N := by positivity
  have hq : 0 ≤ (2 + ‖h₀ τ‖) ^ M := by positivity
  have := hC τ
  have := hD τ
  simp only [Pi.add_apply]
  nlinarith [le_abs_self C, le_abs_self D, abs_nonneg C, abs_nonneg D]

theorem mul {u v : ℍ → ℝ} (hu : PolyBdd h₀ u) (hv : PolyBdd h₀ v) (hu0 : ∀ τ, 0 ≤ u τ)
    (hv0 : ∀ τ, 0 ≤ v τ) : PolyBdd h₀ (u * v) := by
  obtain ⟨C, N, hC⟩ := hu
  obtain ⟨D, M, hD⟩ := hv
  refine ⟨C * D, N + M, fun τ ↦ ?_⟩
  simp only [Pi.mul_apply, pow_add]
  have := mul_le_mul (hC τ) (hD τ) (hv0 τ) ((hu0 τ).trans (hC τ))
  linarith

end PolyBdd

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
