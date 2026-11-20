/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original path Oka/Uniformization/R3.lean
-/
import Solutions.Source_ReferenceIutCanLiftCosetCoefficientDescent
import Solutions.Source_ReferenceIutCanLiftFirstCoordinateFibres
import Solutions.Source_ReferenceIutCanLiftRatFuncPoly
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.Polynomial

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

open Polynomial UpperHalfPlane
open scoped MatrixGroups

private def invariantPolynomials (F : ℍ → ℂ) (N : Subgroup SL(2, ℝ)) : Subalgebra ℂ ℂ[X] where
  carrier := {p | ∀ n ∈ N, ∀ τ : ℍ, p.eval (F (n • τ)) = p.eval (F τ)}
  mul_mem' {p q} hp hq n hn τ := by simp only [eval_mul, hp n hn τ, hq n hn τ]
  add_mem' {p q} hp hq n hn τ := by simp only [eval_add, hp n hn τ, hq n hn τ]
  algebraMap_mem' c n _ τ := by simp

namespace IsUniformization

variable {W : WeierstrassCurve ℂ} {A B : SL(2, ℝ)} {π : ℂ → ℂ × ℂ}

/-- A nonconstant polynomial in the first coordinate whose fibers are the `N`-orbits. -/
theorem exists_invariant_polynomial_generator (h : IsUniformization W A B π)
    {Γ N : Subgroup SL(2, ℝ)} (hΓN : Γ ≤ N) (hfin : Γ.relIndex N ≠ 0)
    (hΓ : ∀ τ τ' : ℍ, (π τ).1 = (π τ').1 ↔ ∃ γ ∈ Γ, γ • τ = τ')
    (hb : ∀ n ∈ N, PolyBdd (fun τ : ℍ ↦ (π τ).1) fun τ ↦ ‖(π (n • τ : ℍ)).1‖) :
    ∃ s : ℂ[X], 0 < s.natDegree ∧
      (∀ n ∈ N, ∀ τ : ℍ, s.eval (π (n • τ : ℍ)).1 = s.eval (π τ).1) ∧
      ∀ τ τ' : ℍ, s.eval (π τ).1 = s.eval (π τ').1 → ∃ n ∈ N, n • τ = τ' := by
  classical
  let F : ℍ → ℂ := fun τ ↦ (π τ).1
  let R := invariantPolynomials F N
  obtain ⟨p, ⟨k, hk⟩, hpInv, hsep⟩ := h.exists_orbit_separating_polynomials hΓN hfin hΓ hb
  have hpR (j : ℕ) : p j ∈ R := hpInv j
  obtain ⟨s, hs, ⟨r, hr, q, hq, hqne, hsq⟩, hcomp⟩ :=
    RatFuncPoly.exists_poly_generator R ⟨p k, hpR k, hk⟩
  have hF : HolH F := by
    refine h.differentiableOn.fst.congr fun z hz ↦ ?_
    change (π (ofComplex z)).1 = (π z).1
    rw [ofComplex_apply_of_im_pos hz]
  have holEval (a : ℂ[X]) : HolH (fun τ ↦ a.eval (F τ)) :=
    (Polynomial.differentiable a).comp_differentiableOn hF
  obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset q.roots.toFinset
  obtain ⟨τ₀, hτ₀⟩ := h.surjective_fst w
  have hq₀ : q.eval (F τ₀) ≠ 0 := by
    rw [show F τ₀ = w from hτ₀]
    exact fun he ↦ hw (Multiset.mem_toFinset.mpr ((mem_roots hqne).mpr he))
  refine ⟨s, hs, ?_, ?_⟩
  · intro n hn τ
    have hqInv : ∀ σ : ℍ, q.eval (F (n • σ)) = q.eval (F σ) := hq n hn
    have hrInv : ∀ σ : ℍ, r.eval (F (n • σ)) = r.eval (F σ) := hr n hn
    let f : ℂ → ℂ := fun z ↦ s.eval (F (n • ofComplex z)) - s.eval (F (ofComplex z))
    let g : ℂ → ℂ := fun z ↦ q.eval (F (ofComplex z))
    have hf : DifferentiableOn ℂ f upperHalfPlaneSet :=
      DifferentiableOn.sub ((holEval s).comp_smul n) (holEval s)
    have hg : DifferentiableOn ℂ g upperHalfPlaneSet := holEval q
    have hprod : ∀ z ∈ upperHalfPlaneSet, f z * g z = 0 := by
      intro z _
      let σ := ofComplex z
      have h₁ := congrArg (eval (F (n • σ))) hsq
      have h₂ := congrArg (eval (F σ)) hsq
      rw [eval_mul, hqInv σ, hrInv σ] at h₁
      rw [eval_mul] at h₂
      change (s.eval (F (n • σ)) - s.eval (F σ)) * q.eval (F σ) = 0
      rw [sub_mul, h₁, h₂, sub_self]
    have hzero := (hf.analyticOnNhd isOpen_upperHalfPlaneSet).eq_zero_or_eq_zero_of_mul_eq_zero
      (hg.analyticOnNhd isOpen_upperHalfPlaneSet) hprod (convex_halfSpace_im_gt 0).isPreconnected
    have hgne : ¬ ∀ z ∈ upperHalfPlaneSet, g z = 0 := by
      intro hz
      apply hq₀
      simpa only [g, ofComplex_apply] using hz (τ₀ : ℂ) τ₀.im_pos
    apply sub_eq_zero.mp
    simpa only [f, ofComplex_apply] using (hzero.resolve_right hgne) (τ : ℂ) τ.im_pos
  · intro τ τ' hEq
    apply (hsep τ τ').mp
    intro k'
    obtain ⟨a, ha⟩ := hcomp (p k') (hpR k')
    rw [ha, eval_comp, eval_comp, hEq]

/-- Finite relative index and polynomial growth give a polynomial whose fibers
are the orbits of the uniformization group's commensurator. -/
theorem exists_invariant_polynomial_generator_for_commensurator [W.IsElliptic]
    (h : IsUniformization W A B π)
    (hfin : (Subgroup.closure {A, B}).relIndex
      (Subgroup.Commensurable.commensurator (Subgroup.closure {A, B})) ≠ 0)
    (hb : ∀ n ∈ Subgroup.Commensurable.commensurator (Subgroup.closure {A, B}),
      PolyBdd (fun τ : ℍ ↦ (π τ).1) fun τ ↦ ‖(π (n • τ : ℍ)).1‖) :
    ∃ s : ℂ[X], 0 < s.natDegree ∧
      (∀ n ∈ Subgroup.Commensurable.commensurator (Subgroup.closure {A, B}),
        ∀ τ : ℍ, s.eval (π (n • τ : ℍ)).1 = s.eval (π τ).1) ∧
      ∀ τ τ' : ℍ, s.eval (π τ).1 = s.eval (π τ').1 →
        ∃ n ∈ Subgroup.Commensurable.commensurator (Subgroup.closure {A, B}), n • τ = τ' := by
  obtain ⟨Γ, hGΓ, hΓN, hΓ⟩ := h.exists_fst_fibre_group
  exact h.exists_invariant_polynomial_generator hΓN
    (fun he ↦ hfin (Subgroup.relIndex_eq_zero_of_le_left hGΓ he)) hΓ hb

end IsUniformization

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
