/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/M2/Final.lean
-/
import Solutions.Source_ReferenceIutCanLiftComplexEmbedding
import Solutions.Source_ReferenceIutCanLiftFrickeUnipotentCommensurator
import Solutions.Source_ReferenceIutCanLiftGoodLattice
import Solutions.Source_ReferenceIutCanLiftNonElementary
import Solutions.Source_ReferenceIutCanLiftSuperrigidity
import Solutions.Source_ReferenceIutCanLiftUnipotentComplex

set_option autoImplicit false

open Set OnePoint OnePoint.Proj
open Subgroup.Commensurable (commensurator)
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2

section ProjectiveAction

variable {k : Type*} [Field k] [DecidableEq k]

lemma slMap_uU_two (σ : ℝ →+* k) (y : OnePoint k) :
    slMap σ (SL2R.uU 2) • y = transl (2 : k) • y := by
  rw [gl_smul_eq_mob, gl_smul_eq_mob, coe_slMap]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [transl, SL2R.uU, map_ofNat]

lemma slMap_neg_one (σ : ℝ →+* k) (y : OnePoint k) : slMap σ (-1) • y = y := by
  rw [gl_smul_eq_mob, coe_slMap]
  have : ((-1 : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).map σ = (-1 : k) • 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [this, mob_smul_matrix (neg_ne_zero.2 one_ne_zero), mob_one]

end ProjectiveAction

open Fricke (nA nB coe_nA coe_nB coe_nAnB)

variable {x y z : ℝ} (hz : 0 < z) (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)

/-- **The complex step.** If the commensurator of a normal-form group is dense, then every ring
embedding `σ : ℝ → ℂ` fixes `x², y², z²`. -/
theorem sq_fixed_of_dense (hx : 0 < x) (hy : 0 < y) (h1 : x < y + z) (h2 : y < x + z)
    (h3 : z < x + y)
    (hdense : Dense (commensurator (Subgroup.closure {nA hz hrel, nB hz hrel}) : Set SL(2, ℝ)))
    (σ : ℝ →+* ℂ) :
    σ x ^ 2 = (x : ℂ) ^ 2 ∧ σ y ^ 2 = (y : ℂ) ^ 2 ∧ σ z ^ 2 = (z : ℂ) ^ 2 := by
  classical
  set Γ := Subgroup.closure {nA hz hrel, nB hz hrel}
  set Δ := commensurator Γ
  have hA : nA hz hrel ∈ Γ := Subgroup.subset_closure (by simp)
  have hB : nB hz hrel ∈ Γ := Subgroup.subset_closure (by simp)
  obtain ⟨Φ, hΦ, hext, hcont⟩ := commensurator_superrigidity (k := ℂ)
    (goodLattice_normal hz hrel hx hy h1 h2 h3) (le_commensurator Γ) le_rfl hdense
    (actsOn_slMap σ Δ)
    (nonElem_slMap hz hrel σ hx.ne')
    (unbounded_complex hz hrel σ)
  have hU2 : SL2R.uU 2 ∈ Δ := uU_two_mem_commensurator hz hrel
  have htr : UnipotentRigidity.IsTransl Φ 2 2 := fun w ↦ by
    rw [hext _ hU2, slMap_uU_two]
  have hneg : ∀ w : OnePoint ℂ, Φ (-1) • w = w := fun w ↦ by
    rw [hext _ (neg_one_mem_commensurator Γ), slMap_neg_one]
  have hmob : ∀ γ ∈ Γ, ∀ w : OnePoint ℂ,
      Φ γ • w = OnePoint.Proj.mob ((γ : Matrix (Fin 2) (Fin 2) ℝ).map σ) w := by
    intro γ hγ w
    rw [hext _ (le_commensurator Γ hγ), gl_smul_eq_mob, coe_slMap]
  have hAB : nA hz hrel * nB hz hrel ∈ Γ := mul_mem hA hB
  have rA := complex_rigidity hΦ hcont htr hneg σ (hmob _ hA)
    (by rw [coe_nA]; simpa using hx.ne')
  have rB := complex_rigidity hΦ hcont htr hneg σ (hmob _ hB)
    (by rw [coe_nB]; simpa using hy.ne')
  have rAB := complex_rigidity hΦ hcont htr hneg σ (hmob _ hAB)
    (by rw [coe_nAnB]; simpa using hz.ne')
  rw [coe_nA] at rA
  rw [coe_nB] at rB
  rw [coe_nAnB] at rAB
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.empty_val', Matrix.cons_val_fin_one, map_neg, neg_sq, Complex.ofReal_neg] at rA rB rAB
  exact ⟨rA, rB, rAB⟩

/-- Consequently `x², y², z²` are rational. -/
theorem sq_rat_of_dense (hx : 0 < x) (hy : 0 < y) (h1 : x < y + z) (h2 : y < x + z)
    (h3 : z < x + y)
    (hdense : Dense (commensurator (Subgroup.closure {nA hz hrel, nB hz hrel}) : Set SL(2, ℝ))) :
    x ^ 2 ∈ Set.range ((↑) : ℚ → ℝ) ∧ y ^ 2 ∈ Set.range ((↑) : ℚ → ℝ) ∧
      z ^ 2 ∈ Set.range ((↑) : ℚ → ℝ) := by
  have key : ∀ w : ℝ, (∀ σ : ℝ →+* ℂ, σ w ^ 2 = (w : ℂ) ^ 2) →
      w ^ 2 ∈ Set.range ((↑) : ℚ → ℝ) := by
    intro w hw
    by_contra hno
    obtain ⟨σ, hσ⟩ := exists_ringHom_real_complex_ne hno
    apply hσ
    rw [map_pow, hw σ, Complex.ofReal_pow]
  exact ⟨key x fun σ ↦ (sq_fixed_of_dense hz hrel hx hy h1 h2 h3 hdense σ).1,
    key y fun σ ↦ (sq_fixed_of_dense hz hrel hx hy h1 h2 h3 hdense σ).2.1,
    key z fun σ ↦ (sq_fixed_of_dense hz hrel hx hy h1 h2 h3 hdense σ).2.2⟩

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2
