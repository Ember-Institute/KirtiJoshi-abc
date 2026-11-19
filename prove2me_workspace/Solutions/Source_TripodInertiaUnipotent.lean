/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 10e40d2e52a8e7220c2a90ff1595f5b385f987ef
Original path Iut/Tripod/InertiaUnipotent.lean
-/
import Solutions.Source_TripodInertiaTransport
import Solutions.Source_TripodMultiplicativeUnipotence
import Solutions.Source_TripodUnramifiedBase

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

section Transport

variable {K : Type*} [Field K] {Γ : Type*}
  [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
  {W : WeierstrassCurve K} (C : VariableChange K) {μ : K} (σ : K →+* K)

private theorem iterate_map_eq_self_after_change
    (h₁ : (C • W).a₁ = 0) (h₂ : (C • W).a₂ = -(1 + μ)) (h₃ : (C • W).a₃ = 0)
    (h₄ : (C • W).a₄ = μ) (h₆ : (C • W).a₆ = 0)
    (hμ : v μ < 1) (h2 : v 2 = 1) (hσμ : σ μ = μ)
    (hσ : ∀ z, v z ≤ 1 → v (σ z - z) < 1) (hvσ : ∀ z, v (σ z) = v z)
    {n : ℕ} (hodd : Odd n) (hn : v (n : K) = 1)
    (φ : W.toAffine.Point →+ W.toAffine.Point)
    (hφ : ∀ (a b : K) (h : W.toAffine.Nonsingular a b),
      ∃ h' : W.toAffine.Nonsingular (σ a) (σ b), φ (.some a b h) = .some (σ a) (σ b) h')
    (hu : σ C.u = C.u) (hr : σ C.r = C.r) (hs : σ C.s = C.s) (ht : σ C.t = C.t)
    (Q : W.toAffine.Point) (hQ : n • Q = 0) : (⇑φ)^[n] Q = Q := by
  let e := Anabelian.vcEquiv C W
  let ψ := e.toAddMonoidHom.comp (φ.comp e.symm.toAddMonoidHom)
  have hQ' : n • e Q = 0 := by rw [← map_nsmul, hQ, map_zero]
  have hiter := MultKernel.iterate_map_eq_self v h₁ h₂ h₃ h₄ h₆ σ hμ h2 hσμ hσ hvσ hodd hn ψ
    (exists_vcEquiv_map_eq C W σ hu hr hs ht φ hφ) (e Q) hQ'
  change (⇑(e.toAddMonoidHom.comp (φ.comp e.symm.toAddMonoidHom)))^[n] (e Q) = e Q at hiter
  rw [iterate_conj] at hiter
  exact e.injective hiter

end Transport

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

private lemma legendreCoeffs_baseChange (μ₀ : k) :
    (Affine.baseChange (legendre μ₀) K).a₁ = 0 ∧
    (Affine.baseChange (legendre μ₀) K).a₂ = -(1 + algebraMap k K μ₀) ∧
    (Affine.baseChange (legendre μ₀) K).a₃ = 0 ∧
    (Affine.baseChange (legendre μ₀) K).a₄ = algebraMap k K μ₀ ∧
    (Affine.baseChange (legendre μ₀) K).a₆ = 0 := by
  rw [legendre_baseChange]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- At an odd bad place, inertia unipotence on prime-to-residue-characteristic torsion of a
Legendre curve follows when the automorphism fixes the square roots used in its models. -/
theorem iterate_map_eq_self_of_inertia (μ₀ : k) (v : FinitePlace K) (h2 : residueChar v ≠ 2)
    {n : ℕ} (hodd : Odd n) (hn : v.maximalIdeal.valuation K (n : K) = 1)
    (hbad : v.maximalIdeal.valuation K (algebraMap k K μ₀) ≠ 1 ∨
      v.maximalIdeal.valuation K (algebraMap k K μ₀ - 1) ≠ 1)
    (σ : K ≃ₐ[k] K) (hσ : σ ∈ v.maximalIdeal.asIdeal.inertia (K ≃ₐ[k] K))
    {i u : K} (hi : i ^ 2 = -1) (hu : u ^ 2 = algebraMap k K μ₀)
    (hσi : σ i = i) (hσu : σ u = u)
    (Q : (Affine.baseChange (legendre μ₀) K).Point) (hQ : n • Q = 0) :
    (⇑(Point.map (W' := legendre μ₀) (S := k) σ.toAlgHom))^[n] Q = Q := by
  let ν := v.maximalIdeal.valuation K
  let μ := algebraMap k K μ₀
  let φ := Point.map (W' := legendre μ₀) (S := k) σ.toAlgHom
  have h2' : ν 2 = 1 := valuation_two_eq_one_of_ne h2
  have hσ' (z : K) (hz : ν z ≤ 1) : ν (σ z - z) < 1 :=
    valuation_sub_lt_one_of_mem_inertia hσ hz
  have hvσ (z : K) : ν (σ z) = ν z := valuation_map_eq_of_mem_inertia hσ z
  obtain ⟨hE₁, hE₂, hE₃, hE₄, hE₆⟩ := legendreCoeffs_baseChange (K := K) μ₀
  have hφ (a b : K) (h : (Affine.baseChange (legendre μ₀) K).Nonsingular a b) :
      ∃ h' : (Affine.baseChange (legendre μ₀) K).Nonsingular (σ a) (σ b),
        φ (.some a b h) = .some (σ a) (σ b) h' :=
    ⟨_, Point.map_some σ.toAlgHom h⟩
  change ν μ ≠ 1 ∨ ν (μ - 1) ≠ 1 at hbad
  rcases lt_trichotomy (ν μ) 1 with hμ | hμ | hμ
  · exact MultKernel.iterate_map_eq_self ν hE₁ hE₂ hE₃ hE₄ hE₆ (σ : K →+* K) hμ h2'
      (σ.commutes _) hσ' hvσ hodd hn φ hφ Q hQ
  · have hne : ν (μ - 1) ≠ 1 := hbad.resolve_left (fun h => h hμ)
    have hle : ν (μ - 1) ≤ 1 :=
      (Valuation.map_sub _ _ _).trans (max_le hμ.le (by rw [map_one]))
    have hμ1 : ν (1 - μ) < 1 := by
      rw [Valuation.map_sub_swap]
      exact lt_of_le_of_ne hle hne
    have hi0 : i ≠ 0 := fun h => by
      rw [h, zero_pow two_ne_zero] at hi
      exact (neg_ne_zero.mpr one_ne_zero) hi.symm
    let C : VariableChange K := ⟨Units.mk0 i hi0, 1, 0, 0⟩
    obtain ⟨hC₁, hC₂, hC₃, hC₄, hC₆⟩ :=
      legendreCoeffs_vc_one_sub hE₁ hE₂ hE₃ hE₄ hE₆ hi hi0
    have hfix : σ (1 - μ) = 1 - μ := by
      change σ (1 - algebraMap k K μ₀) = _
      rw [map_sub, map_one, σ.commutes]
    exact iterate_map_eq_self_after_change ν C (σ : K →+* K) hC₁ hC₂ hC₃ hC₄ hC₆
      hμ1 h2' hfix hσ' hvσ hodd hn φ hφ hσi (map_one _) (map_zero _) (map_zero _) Q hQ
  · have hμ0 : μ ≠ 0 := fun h => by
      rw [h, map_zero] at hμ
      exact (not_lt.mpr zero_le_one) hμ
    have hμ1 : ν μ⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ hμ
    have hu0 : u ≠ 0 := fun h => hμ0 (by
      change algebraMap k K μ₀ = 0
      rw [← hu, h, zero_pow two_ne_zero])
    let C : VariableChange K := ⟨Units.mk0 u hu0, 0, 0, 0⟩
    obtain ⟨hC₁, hC₂, hC₃, hC₄, hC₆⟩ :=
      legendreCoeffs_vc_inv hE₁ hE₂ hE₃ hE₄ hE₆ hu hu0
    have hfix : σ μ⁻¹ = μ⁻¹ := by
      change σ (algebraMap k K μ₀)⁻¹ = _
      rw [map_inv₀, σ.commutes]
    exact iterate_map_eq_self_after_change ν C (σ : K →+* K) hC₁ hC₂ hC₃ hC₄ hC₆
      hμ1 h2' hfix hσ' hvσ hodd hn φ hφ hσu (map_zero _) (map_zero _) (map_zero _) Q hQ

end AbcAdaptation.Tripod
