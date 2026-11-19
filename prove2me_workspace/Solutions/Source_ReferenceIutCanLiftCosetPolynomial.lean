/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original path Oka/Uniformization/R3.lean
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.GroupTheory.Index

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

open Polynomial UpperHalfPlane
open scoped BigOperators MatrixGroups

/-- The product over the inverses of representatives of `N / Γ` is invariant under `N`.
When the fibers of `F` are the `Γ)-orbits, the coefficients of this product have the
`N)-orbits as their common fibers. -/
theorem exists_coset_polynomial {Γ N : Subgroup SL(2, ℝ)} {F : ℍ → ℂ}
    (hΓN : Γ ≤ N) (hfin : Γ.relIndex N ≠ 0)
    (hinv : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ)
    (hfib : ∀ τ τ' : ℍ, F τ = F τ' → ∃ γ ∈ Γ, γ • τ = τ') :
    ∃ (ι : Type) (_ : Fintype ι) (g : ι → SL(2, ℝ)),
      let P : ℍ → ℂ[X] := fun τ ↦ ∏ i, (X - C (F (g i • τ)))
      (∀ i, g i ∈ N) ∧ (∀ τ, (P τ).Monic) ∧ (∀ τ, (P τ).eval (F τ) = 0) ∧
        (∀ n ∈ N, ∀ τ, P (n • τ) = P τ) ∧
        ∀ τ τ' : ℍ, (∀ k : ℕ, (P τ).coeff k = (P τ').coeff k) ↔ ∃ n ∈ N, n • τ = τ' := by
  classical
  letI : (Γ.subgroupOf N).FiniteIndex := ⟨hfin⟩
  letI := Fintype.ofFinite (N ⧸ Γ.subgroupOf N)
  let g : N ⧸ Γ.subgroupOf N → SL(2, ℝ) := fun q ↦ ((q.out : N) : SL(2, ℝ))⁻¹
  let f : (N ⧸ Γ.subgroupOf N) → ℍ → ℂ := fun q τ ↦ F (g q • τ)
  let P : ℍ → ℂ[X] := fun τ ↦ ∏ q, (X - C (f q τ))
  have hgN (q : N ⧸ Γ.subgroupOf N) : g q ∈ N := N.inv_mem (q.out : N).2
  have hrep (x : N) (τ : ℍ) :
      f (QuotientGroup.mk x) τ = F (((x : SL(2, ℝ)))⁻¹ • τ) := by
    obtain ⟨γ, hγ⟩ := QuotientGroup.mk_out_eq_mul (Γ.subgroupOf N) x
    have hγΓ : ((γ : N) : SL(2, ℝ)) ∈ Γ := Subgroup.mem_subgroupOf.mp γ.2
    simp only [f, g, hγ, Subgroup.coe_mul, mul_inv_rev, mul_smul]
    exact hinv _ (Γ.inv_mem hγΓ) _
  have hPInv (n : SL(2, ℝ)) (hn : n ∈ N) (τ : ℍ) : P (n • τ) = P τ := by
    let n' : N := ⟨n, hn⟩
    have hperm (q : N ⧸ Γ.subgroupOf N) : f q (n • τ) = f (n'⁻¹ • q) τ := by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      rw [MulAction.Quotient.smul_mk, hrep, hrep, smul_eq_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        mul_inv_rev, inv_inv, mul_smul]
    simp only [P, hperm]
    exact Fintype.prod_equiv (MulAction.toPerm n'⁻¹) _ _ fun q ↦ rfl
  have hroot (τ : ℍ) : (P τ).eval (F τ) = 0 := by
    simp only [P, eval_prod, eval_sub, eval_X, eval_C]
    refine Finset.prod_eq_zero (Finset.mem_univ (QuotientGroup.mk 1 : N ⧸ Γ.subgroupOf N)) ?_
    rw [hrep, Subgroup.coe_one, inv_one, one_smul, sub_self]
  refine ⟨N ⧸ Γ.subgroupOf N, inferInstance, g, hgN,
    fun τ ↦ monic_prod_X_sub_C (fun q ↦ f q τ) Finset.univ, hroot, hPInv, ?_⟩
  change ∀ τ τ' : ℍ, (∀ k : ℕ, (P τ).coeff k = (P τ').coeff k) ↔ ∃ n ∈ N, n • τ = τ'
  intro τ τ'
  constructor
  · intro hcoeff
    have hzero : (P τ).eval (F τ') = 0 := by
      rw [Polynomial.ext hcoeff]
      exact hroot τ'
    simp only [P, eval_prod, eval_sub, eval_X, eval_C, Finset.prod_eq_zero_iff, Finset.mem_univ,
      true_and, sub_eq_zero] at hzero
    obtain ⟨q, hq⟩ := hzero
    obtain ⟨γ, hγ, hmove⟩ := hfib (g q • τ) τ' hq.symm
    exact ⟨γ * g q, N.mul_mem (hΓN hγ) (hgN q), (mul_smul _ _ _).trans hmove⟩
  · rintro ⟨n, hn, rfl⟩ k
    rw [hPInv n hn τ]

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
