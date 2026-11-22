/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/StableTwo.lean
-/
import Solutions.Source_ReferenceIutThreeTorsionNormalForm
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FinitePlaceResidueTransport

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open WeierstrassCurve WithZero
open scoped WithZero

/-! ## Stable models from two independent flexes -/

section Curve

variable {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰)

/-- Every model has an integral change of variables (Mathlib's `exists_isIntegral` over the
valuation subring). -/
private lemma exists_variableChange_isIntegralModel (E : WeierstrassCurve K) :
    ∃ C : VariableChange K, IsIntegralModel v (C • E) := by
  obtain ⟨C, hC⟩ := exists_isIntegral v.valuationSubring E
  refine ⟨C, ?_⟩
  obtain ⟨W₀, hW₀⟩ := hC.integral
  have key : ∀ r : v.valuationSubring, v (algebraMap v.valuationSubring K r) ≤ 1 := fun r => r.2
  rw [hW₀]
  exact ⟨key _, key _, key _, key _, key _⟩

/-- **A stable model from two flexes with distinct `x`-coordinates** on an integral model, for
`v(3) = 1` and a uniformizer `π`. -/
private theorem exists_isStableModel_of_flex (h3 : v 3 = 1) {π : K} (hπ : v π = exp (-1))
    {W : WeierstrassCurve K} (hW : IsIntegralModel v W) (d₁ d₂ : FlexData W)
    (hx : d₁.x ≠ d₂.x) : ∃ C : VariableChange K, IsStableModel v (C • W) := by
  have hx₁ := d₁.valuation_x_le_one v hW h3
  have hy₁ := d₁.valuation_y_le_one v hW hx₁
  have hl₁ := d₁.valuation_lam_le_one v hW hx₁
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := hW
  set C₁ : VariableChange K := ⟨1, d₁.x, d₁.lam, d₁.y⟩ with hC₁
  set A : K := W.a₁ + 2 * d₁.lam with hA
  set B : K := W.a₃ + d₁.x * W.a₁ + 2 * d₁.y with hB
  have hN : C₁ • W = normalForm A B := d₁.variableChange_eq
  have hAv : v A ≤ 1 := by
    rw [hA, ← Valuation.mem_integer_iff] at *
    exact add_mem h₁ (mul_mem (ofNat_mem _ 2) hl₁)
  have hBv : v B ≤ 1 := by
    rw [hB, ← Valuation.mem_integer_iff] at *
    exact add_mem (add_mem h₃ (mul_mem hx₁ h₁)) (mul_mem (ofNat_mem _ 2) hy₁)
  have hB0 : B ≠ 0 := by
    intro h
    apply d₁.ne
    rw [← h, hB]
    ring
  obtain ⟨n, hn⟩ := exists_nat_eq_exp_neg ((Valuation.ne_zero_iff v).2 hB0) hBv
  -- the second flex in the normal form
  set d := d₂.variableChange C₁ with hd
  have hdx : d.x = d₂.x - d₁.x := by
    rw [hd, FlexData.variableChange_x, hC₁]
    simp
  have hdx0 : d.x ≠ 0 := by
    rw [hdx]
    exact sub_ne_zero.mpr (Ne.symm hx)
  have hψ := d.psi3
  have hb₂ : (C₁ • W).b₂ = A ^ 2 := by rw [hN, normalForm_b₂]
  have hb₄ : (C₁ • W).b₄ = A * B := by rw [hN, normalForm_b₄]
  have hb₆ : (C₁ • W).b₆ = B ^ 2 := by rw [hN, normalForm_b₆]
  have hb₈ : (C₁ • W).b₈ = 0 := by rw [hN, normalForm_b₈]
  rw [hb₂, hb₄, hb₆, hb₈] at hψ
  have hg : 3 * d.x ^ 3 + A ^ 2 * d.x ^ 2 + 3 * A * B * d.x + 3 * B ^ 2 = 0 := by
    have : d.x * (3 * d.x ^ 3 + A ^ 2 * d.x ^ 2 + 3 * A * B * d.x + 3 * B ^ 2) = 0 := by
      linear_combination hψ
    exact (mul_eq_zero.mp this).resolve_left hdx0
  obtain ⟨C, hC⟩ := exists_isStableModel_normalForm v h3 hπ n A B d.x hAv hn hdx0 hg
  refine ⟨C * C₁, ?_⟩
  rw [mul_smul, hN]
  exact hC

/-- **A stable model from two flexes with distinct `x`-coordinates** on an arbitrary model. -/
private theorem exists_isStableModel_of_two_flexes (h3 : v 3 = 1) {π : K} (hπ : v π = exp (-1))
    (W : WeierstrassCurve K) (d₁ d₂ : FlexData W) (hx : d₁.x ≠ d₂.x) :
    ∃ C : VariableChange K, IsStableModel v (C • W) := by
  obtain ⟨C₀, hC₀⟩ := exists_variableChange_isIntegralModel v W
  have hx' : (d₁.variableChange C₀).x ≠ (d₂.variableChange C₀).x := by
    simp only [FlexData.variableChange_x]
    intro h
    apply hx
    have hu : (C₀.u : K)⁻¹ ^ 2 ≠ 0 := pow_ne_zero _ (inv_ne_zero C₀.u.ne_zero)
    have := mul_left_cancel₀ hu h
    linear_combination this
  obtain ⟨C, hC⟩ := exists_isStableModel_of_flex v h3 hπ hC₀ (d₁.variableChange C₀)
    (d₂.variableChange C₀) hx'
  exact ⟨C * C₀, by rw [mul_smul]; exact hC⟩

end Curve

/-! ## Stable reduction from rational `3`-torsion -/

section Place

open NumberField IsDedekindDomain.HeightOneSpectrum

variable {F : Type*} [Field F] [NumberField F] [DecidableEq F]

/-- **Raynaud's criterion for `n = 3`, away from `3`**: an elliptic curve `E/F` with two
rational points `P`, `Q` of order `3`, `Q ∉ ⟨P⟩`, has stable reduction at every finite place
of residue characteristic `≠ 3`. -/
theorem hasStableReductionAt_of_three_torsion (E : WeierstrassCurve F) (w : FinitePlace F)
    (hw : residueChar w ≠ 3) (P Q : E.toAffine.Point) (hP : 3 • P = 0) (hQ : 3 • Q = 0)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (hQP : Q ≠ P) (hQP' : Q ≠ -P) : HasStableReductionAt E w := by
  have h3Nat : w.maximalIdeal.valuation F ((3 : ℕ) : F) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 F) F), valuation_eq_one_iff_notMem,
      natCast_mem_maximalIdeal_iff w Nat.prime_three]
    exact hw
  have h3 : w.maximalIdeal.valuation F 3 = 1 := by
    simpa only [Nat.cast_ofNat] using h3Nat
  obtain ⟨π, hπ⟩ := w.maximalIdeal.valuation_exists_uniformizer F
  cases P with
  | zero => exact absurd rfl hP0
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => exact absurd rfl hQ0
    | some x₂ y₂ h₂ =>
      have hx : x₁ ≠ x₂ := by
        intro hx
        rcases Affine.Point.X_eq_iff.mp hx with h | h
        · exact hQP h.symm
        · exact hQP' (by rw [h, neg_neg])
      obtain ⟨C, hC⟩ := exists_isStableModel_of_two_flexes (w.maximalIdeal.valuation F) h3 hπ E
        (FlexData.ofPoint h₁ hP) (FlexData.ofPoint h₂ hQ) (by simpa using hx)
      exact hasStableReductionAt_of_isStableModel E w C hC

end Place

end AbcAdaptation.Reference.Iut
