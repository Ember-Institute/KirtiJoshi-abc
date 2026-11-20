/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original path Oka/Uniformization/R3.lean
-/
import Solutions.Source_ReferenceIutCanLiftAnalyticLiftFacts
import Solutions.Source_ReferenceIutCanLiftCosetPolynomial
import Solutions.Source_ReferenceIutCanLiftPolynomialDescent

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.IsUniformization

open Polynomial UpperHalfPlane
open scoped BigOperators MatrixGroups

variable {W : WeierstrassCurve ℂ} {A B : SL(2, ℝ)} {π : ℂ → ℂ × ℂ}

/-- The coset coefficients descend to polynomials in the first coordinate. Together they
separate the `N`-orbits, and at least one has positive degree. -/
theorem exists_orbit_separating_polynomials (h : IsUniformization W A B π)
    {Γ N : Subgroup SL(2, ℝ)} (hΓN : Γ ≤ N) (hfin : Γ.relIndex N ≠ 0)
    (hΓ : ∀ τ τ' : ℍ, (π τ).1 = (π τ').1 ↔ ∃ γ ∈ Γ, γ • τ = τ')
    (hb : ∀ n ∈ N, PolyBdd (fun τ : ℍ ↦ (π τ).1) fun τ ↦ ‖(π (n • τ : ℍ)).1‖) :
    ∃ p : ℕ → ℂ[X], (∃ k, 0 < (p k).natDegree) ∧
      (∀ k, ∀ n ∈ N, ∀ τ : ℍ, (p k).eval (π (n • τ : ℍ)).1 = (p k).eval (π τ).1) ∧
      ∀ τ τ' : ℍ, (∀ k, (p k).eval (π τ).1 = (p k).eval (π τ').1) ↔
        ∃ n ∈ N, n • τ = τ' := by
  classical
  let F : ℍ → ℂ := fun τ ↦ (π τ).1
  have hF : HolH F := by
    refine h.differentiableOn.fst.congr fun z hz ↦ ?_
    change (π (ofComplex z)).1 = (π z).1
    rw [ofComplex_apply_of_im_pos hz]
  have hinv (γ : SL(2, ℝ)) (hγ : γ ∈ Γ) (τ : ℍ) : F (γ • τ) = F τ :=
    ((hΓ τ (γ • τ)).mpr ⟨γ, hγ, rfl⟩).symm
  obtain ⟨ι, hι, g, hg, hmonic, hroot, hPInv, hPsep⟩ :=
    exists_coset_polynomial hΓN hfin hinv (fun τ τ' hEq ↦ (hΓ τ τ').mp hEq)
  letI : Fintype ι := hι
  let P : ℍ → ℂ[X] := fun τ ↦ ∏ i, (X - C (F (g i • τ)))
  have hcoeff (k : ℕ) : ∃ p : ℂ[X], ∀ τ : ℍ, p.eval (F τ) = (P τ).coeff k := by
    refine h.exists_polynomial_of_fst_fibres ?_ ?_ ?_
    · exact differentiableOn_coeff_prod_X_sub_C Finset.univ
        (a := fun i z ↦ F (g i • ofComplex z)) (fun i _ ↦ hF.comp_smul (g i)) k
    · intro τ τ' hEq
      obtain ⟨γ, hγ, hmove⟩ := (hΓ τ τ').mp hEq
      exact (congrArg (fun Q : ℂ[X] ↦ Q.coeff k) (hPInv γ (hΓN hγ) τ)).symm.trans
        (congrArg (fun σ : ℍ ↦ (P σ).coeff k) hmove)
    · exact (PolyBdd.prod Finset.univ (u := fun i τ ↦ 1 + ‖F (g i • τ)‖)
        (fun i _ ↦ (PolyBdd.const 1).add (hb (g i) (hg i)))
        (fun i _ τ ↦ add_nonneg zero_le_one (norm_nonneg (F (g i • τ))))).mono
        (fun τ ↦ norm_coeff_prod_X_sub_C_le Finset.univ (fun i ↦ F (g i • τ)) k)
  choose p hp using hcoeff
  refine ⟨p, ?_, ?_, ?_⟩
  · by_contra hnc
    have hdeg (k : ℕ) : (p k).natDegree = 0 :=
      Nat.eq_zero_of_not_pos (fun hk ↦ hnc ⟨k, hk⟩)
    have hconst (τ τ' : ℍ) : P τ = P τ' := by
      apply Polynomial.ext
      intro k
      rw [← hp k τ, ← hp k τ', eq_C_of_natDegree_eq_zero (hdeg k), eval_C, eval_C]
    obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (P UpperHalfPlane.I).roots.toFinset
    obtain ⟨τ, hτ⟩ := h.surjective_fst w
    apply hw
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots (hmonic UpperHalfPlane.I).ne_zero).mpr
    change (P UpperHalfPlane.I).eval w = 0
    rw [← show F τ = w from hτ, hconst UpperHalfPlane.I τ]
    exact hroot τ
  · intro k n hn τ
    calc
      (p k).eval (F (n • τ)) = (P (n • τ)).coeff k := hp k (n • τ)
      _ = (P τ).coeff k := congrArg (fun Q : ℂ[X] ↦ Q.coeff k) (hPInv n hn τ)
      _ = (p k).eval (F τ) := (hp k τ).symm
  · intro τ τ'
    have hEq :
        (∀ k, (p k).eval (F τ) = (p k).eval (F τ')) ↔
        (∀ k, (P τ).coeff k = (P τ').coeff k) := by
      simp only [hp]
    exact hEq.trans (hPsep τ τ')

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.IsUniformization
