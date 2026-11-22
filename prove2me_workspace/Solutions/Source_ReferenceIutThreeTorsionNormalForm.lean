/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/StableTwo.lean
-/
import Solutions.Source_ReferenceIutTorsionFlex
import Mathlib.Tactic.Push

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open WeierstrassCurve WithZero
open scoped WithZero

/-! ## The normal form `y² + Axy + By = x³` -/

section NormalForm

variable {K : Type*} [Field K]

/-- The Weierstrass curve `y² + Axy + By = x³`. -/
def normalForm (A B : K) : WeierstrassCurve K := ⟨A, 0, B, 0, 0⟩

variable (A B : K)

@[simp] lemma normalForm_a₁ : (normalForm A B).a₁ = A := rfl
@[simp] lemma normalForm_a₂ : (normalForm A B).a₂ = 0 := rfl
@[simp] lemma normalForm_a₃ : (normalForm A B).a₃ = B := rfl
@[simp] lemma normalForm_a₄ : (normalForm A B).a₄ = 0 := rfl
@[simp] lemma normalForm_a₆ : (normalForm A B).a₆ = 0 := rfl

lemma normalForm_b₂ : (normalForm A B).b₂ = A ^ 2 := by
  simp only [b₂, normalForm_a₁, normalForm_a₂]
  ring

lemma normalForm_b₄ : (normalForm A B).b₄ = A * B := by
  simp only [b₄, normalForm_a₁, normalForm_a₃, normalForm_a₄]
  ring

lemma normalForm_b₆ : (normalForm A B).b₆ = B ^ 2 := by
  simp only [b₆, normalForm_a₃, normalForm_a₆]
  ring

lemma normalForm_b₈ : (normalForm A B).b₈ = 0 := by
  simp only [b₈, normalForm_a₁, normalForm_a₂, normalForm_a₃, normalForm_a₄, normalForm_a₆]
  ring

/-- `Δ(y² + Axy + By = x³) = B³(A³ − 27B)`. -/
private lemma normalForm_Δ : (normalForm A B).Δ = B ^ 3 * (A ^ 3 - 27 * B) := by
  simp only [Δ, normalForm_b₂, normalForm_b₄, normalForm_b₆, normalForm_b₈]
  ring

/-- `c₄(y² + Axy + By = x³) = A(A³ − 24B)`. -/
private lemma normalForm_c₄ : (normalForm A B).c₄ = A * (A ^ 3 - 24 * B) := by
  simp only [c₄, normalForm_b₂, normalForm_b₄]
  ring

/-- Rescaling the normal form by `u = π`: `(A, B) ↦ (A/π, B/π³)`. -/
private lemma normalForm_scale {π : K} (hπ : π ≠ 0) :
    (⟨Units.mk0 π hπ, 0, 0, 0⟩ : VariableChange K) • normalForm A B =
      normalForm (π⁻¹ * A) (π⁻¹ ^ 3 * B) := by
  ext <;> simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, normalForm_a₁, normalForm_a₂, normalForm_a₃, normalForm_a₄, normalForm_a₆,
    Units.val_inv_eq_inv_val, Units.val_mk0] <;> ring

end NormalForm

section WithZero

/-- A nonzero element `a ≤ 1` of `ℤᵐ⁰` is `exp(−n)` for a natural number `n`. -/
lemma exists_nat_eq_exp_neg {a : ℤᵐ⁰} (h0 : a ≠ 0) (h1 : a ≤ 1) :
    ∃ n : ℕ, a = exp (-(n : ℤ)) := by
  refine ⟨(-log a).toNat, ?_⟩
  have hlog : log a ≤ 0 := by
    rw [← exp_le_exp, exp_log h0, exp_zero]
    exact h1
  rw [Int.toNat_of_nonneg (by omega), neg_neg, exp_log h0]

/-- `a < exp m` implies `a ≤ exp (m − 1)` in `ℤᵐ⁰`. -/
private lemma le_exp_sub_one_of_lt_exp {a : ℤᵐ⁰} {m : ℤ} (h : a < exp m) : a ≤ exp (m - 1) := by
  rcases eq_or_ne a 0 with rfl | h0
  · exact zero_le
  · rw [← exp_log h0, exp_lt_exp] at h
    rw [← exp_log h0, exp_le_exp]
    omega

/-- `a < 1` implies `a ≤ exp (−1)` in `ℤᵐ⁰`. -/
private lemma le_exp_neg_one_of_lt_one {a : ℤᵐ⁰} (h : a < 1) : a ≤ exp (-1) := by
  have := le_exp_sub_one_of_lt_exp (m := 0) (by rwa [exp_zero])
  rwa [zero_sub] at this

end WithZero

/-! ## Descent in the normal form -/

section Descent

variable {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰)

/-- `v(n) ≤ 1` for a numeral `n`. -/
private lemma valuation_ofNat_le_one (n : ℕ) [n.AtLeastTwo] : v (OfNat.ofNat n : K) ≤ 1 :=
  (Valuation.mem_integer_iff v _).1 (ofNat_mem v.integer n)

/-- The normal form with integral `A`, `B` is an integral model. -/
private lemma isIntegralModel_normalForm {A B : K} (hA : v A ≤ 1) (hB : v B ≤ 1) :
    IsIntegralModel v (normalForm A B) :=
  ⟨hA, by simp, hB, by simp, by simp⟩

/-- **The normal form with a unit `B`** is good or multiplicative (`v(3) = 1`): if `Δ` is not a
unit then `A³ ≡ 27B` is a unit and `c₄ = A(A³ − 24B) ≡ 3AB` is a unit. -/
private lemma isStableModel_normalForm_of_unit (h3 : v 3 = 1) {A B : K} (hA : v A ≤ 1) (hB : v B = 1) :
    IsStableModel v (normalForm A B) := by
  have hint := isIntegralModel_normalForm v hA hB.le
  by_cases hΔ : v (normalForm A B).Δ = 1
  · exact Or.inl ⟨hint, hΔ⟩
  · right
    have hΔ' : v (normalForm A B).Δ < 1 := lt_of_le_of_ne hint.Δ hΔ
    refine ⟨hint, hΔ', ?_⟩
    rw [normalForm_Δ, map_mul, map_pow, hB, one_pow, one_mul] at hΔ'
    have h27 : v (27 * B) = 1 := by
      have : (27 : K) = 3 ^ 3 := by norm_num
      rw [map_mul, this, map_pow, h3, one_pow, one_mul, hB]
    have hA3 : v (A ^ 3) = 1 := by
      have e : A ^ 3 = (A ^ 3 - 27 * B) + 27 * B := by ring
      rw [e, Valuation.map_add_eq_of_lt_right v (by rw [h27]; exact hΔ'), h27]
    have hA1 : v A = 1 := by
      rw [map_pow] at hA3
      exact (pow_eq_one_iff_of_nonneg zero_le (by norm_num)).mp hA3
    have h3B : v (3 * B) = 1 := by rw [map_mul, h3, hB, one_mul]
    rw [normalForm_c₄, map_mul, hA1, one_mul]
    have e : A ^ 3 - 24 * B = (A ^ 3 - 27 * B) + 3 * B := by ring
    rw [e, Valuation.map_add_eq_of_lt_right v (by rw [h3B]; exact hΔ'), h3B]

/-- **The normal form with a unit `A` and a non-unit `B`** is multiplicative. -/
private lemma isMultModel_normalForm_of_unit_left {A B : K} (hA : v A = 1) (hB : v B < 1) :
    IsMultModel v (normalForm A B) := by
  have hint := isIntegralModel_normalForm v hA.le hB.le
  have hA3 : v (A ^ 3) = 1 := by rw [map_pow, hA, one_pow]
  refine ⟨hint, ?_, ?_⟩
  · rw [normalForm_Δ, map_mul, map_pow]
    have h27 : v (27 * B) < 1 := by
      rw [map_mul]
      exact (mul_le_of_le_one_left zero_le (valuation_ofNat_le_one v 27)).trans_lt hB
    rw [Valuation.map_sub_eq_of_lt_left v (by rw [hA3]; exact h27), hA3, mul_one]
    exact pow_lt_one₀ zero_le hB (by norm_num)
  · rw [normalForm_c₄, map_mul, hA, one_mul]
    have h24 : v (24 * B) < 1 := by
      rw [map_mul]
      exact (mul_le_of_le_one_left zero_le (valuation_ofNat_le_one v 24)).trans_lt hB
    rw [Valuation.map_sub_eq_of_lt_left v (by rw [hA3]; exact h24), hA3]

/-- **The dominant-term argument**: if `A` is not a unit, `v(B) = exp(−n)` with `n ∈ {1, 2}`,
then `g(x) = 3x³ + A²x² + 3ABx + 3B²` has no nonzero integral root (`v(3) = 1`). -/
private lemma normalForm_no_root (h3 : v 3 = 1) {A B x : K} {n : ℕ} (hn : n = 1 ∨ n = 2)
    (hA : v A ≤ exp (-1)) (hB : v B = exp (-(n : ℤ))) (hx0 : x ≠ 0) (hx1 : v x ≤ 1)
    (hg : 3 * x ^ 3 + A ^ 2 * x ^ 2 + 3 * A * B * x + 3 * B ^ 2 = 0) : False := by
  have hvx : v x ≠ 0 := (Valuation.ne_zero_iff v).2 hx0
  set m : ℤ := log (v x) with hm
  have hxm : v x = exp m := (exp_log hvx).symm
  have hm0 : m ≤ 0 := by
    rw [← exp_le_exp, ← hxm, exp_zero]
    exact hx1
  -- the valuations of the four terms
  have hT3 : v (3 * x ^ 3) = exp (3 * m) := by
    rw [map_mul, h3, one_mul, map_pow, hxm, ← exp_nsmul, nsmul_eq_mul, Nat.cast_ofNat]
  have hT2 : v (A ^ 2 * x ^ 2) ≤ exp (2 * m - 2) := by
    rw [map_mul, map_pow, map_pow, hxm]
    refine (mul_le_mul_left (pow_le_pow_left₀ zero_le hA 2) _).trans (le_of_eq ?_)
    rw [← exp_nsmul, ← exp_nsmul, ← exp_add, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
    congr 1
    ring
  have hT1 : v (3 * A * B * x) ≤ exp (m - 1 - n) := by
    rw [map_mul, map_mul, map_mul, h3, one_mul, hB, hxm]
    refine (mul_le_mul_left (mul_le_mul_left hA _) _).trans (le_of_eq ?_)
    rw [← exp_add, ← exp_add]
    congr 1
    ring
  have hT0 : v (3 * B ^ 2) = exp (-2 * (n : ℤ)) := by
    rw [map_mul, h3, one_mul, map_pow, hB, ← exp_nsmul, nsmul_eq_mul, Nat.cast_ofNat]
    congr 1
    ring
  by_cases hcase : -2 * (n : ℤ) < 3 * m
  · -- the term `3x³` dominates
    have hlt : v (A ^ 2 * x ^ 2 + 3 * A * B * x + 3 * B ^ 2) < v (3 * x ^ 3) := by
      rw [hT3]
      refine v.map_add_lt (v.map_add_lt ?_ ?_) ?_
      · exact hT2.trans_lt (exp_lt_exp.2 (by omega))
      · exact hT1.trans_lt (exp_lt_exp.2 (by omega))
      · exact hT0.trans_lt (exp_lt_exp.2 (by omega))
    have hS := Valuation.map_add_eq_of_lt_left v hlt
    have e : 3 * x ^ 3 + (A ^ 2 * x ^ 2 + 3 * A * B * x + 3 * B ^ 2) = 0 := by
      linear_combination hg
    rw [e, map_zero, hT3] at hS
    exact exp_ne_zero hS.symm
  · -- the term `3B²` dominates
    have hlt : v (3 * x ^ 3 + A ^ 2 * x ^ 2 + 3 * A * B * x) < v (3 * B ^ 2) := by
      rw [hT0]
      refine v.map_add_lt (v.map_add_lt ?_ ?_) ?_
      · exact hT3.le.trans_lt (exp_lt_exp.2 (by omega))
      · exact hT2.trans_lt (exp_lt_exp.2 (by omega))
      · exact hT1.trans_lt (exp_lt_exp.2 (by omega))
    have hS := Valuation.map_add_eq_of_lt_right v hlt
    rw [hg, map_zero, hT0] at hS
    exact exp_ne_zero hS.symm

/-- **Descent in the normal form**: for `v(3) = 1`, a uniformizer `π`, integral `A`, `B` with
`v(B) = exp(−n)` and a nonzero root `x` of `g = 3x³ + A²x² + 3ABx + 3B²` (the `x`-coordinate
of a second flex), some change of variables of `y² + Axy + By = x³` is a good or
multiplicative model. By strong induction on `n`: the cases of a unit `B` or a unit `A` are
settled directly, `n ∈ {1, 2}` with a non-unit `A` is impossible, and otherwise
`(A, B, x) ↦ (A/π, B/π³, x/π²)` lowers `n` by `3`. -/
theorem exists_isStableModel_normalForm (h3 : v 3 = 1) {π : K} (hπ : v π = exp (-1)) (n : ℕ) :
    ∀ A B x : K, v A ≤ 1 → v B = exp (-(n : ℤ)) → x ≠ 0 →
      3 * x ^ 3 + A ^ 2 * x ^ 2 + 3 * A * B * x + 3 * B ^ 2 = 0 →
      ∃ C : VariableChange K, IsStableModel v (C • normalForm A B) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A B x hA hB hx0 hg
    have hB1 : v B ≤ 1 := by
      rw [hB, ← exp_zero, exp_le_exp]
      omega
    -- `x` is integral: it is a root of `ψ₃ = x · g(x)`
    have hx1 : v x ≤ 1 := by
      refine valuation_le_one_of_quartic v h3 (c₃ := A ^ 2) (c₂ := 3 * A * B) (c₁ := 3 * B ^ 2)
        (c₀ := 0) (by linear_combination x * hg) ?_ ?_ ?_ (by simp)
      · rw [map_pow]; exact pow_le_one₀ zero_le hA
      · rw [map_mul, map_mul, h3, one_mul]; exact mul_le_one' hA hB1
      · rw [map_mul, map_pow, h3, one_mul]; exact pow_le_one₀ zero_le hB1
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · -- `B` is a unit
      subst hn0
      refine ⟨1, ?_⟩
      rw [one_smul]
      exact isStableModel_normalForm_of_unit v h3 hA (by rw [hB]; simp)
    by_cases hA1 : v A = 1
    · -- `A` is a unit
      refine ⟨1, ?_⟩
      rw [one_smul]
      refine Or.inr (isMultModel_normalForm_of_unit_left v hA1 ?_)
      rw [hB, ← exp_zero, exp_lt_exp]
      omega
    have hA' : v A ≤ exp (-1) := le_exp_neg_one_of_lt_one (lt_of_le_of_ne hA hA1)
    rcases lt_or_ge n 3 with hn3 | hn3
    · -- `n ∈ {1, 2}`: impossible
      exact (normalForm_no_root v h3 (by omega) hA' hB hx0 hx1 hg).elim
    · -- `n ≥ 3`: rescale
      have hπ0 : π ≠ 0 := by
        rintro rfl
        rw [map_zero] at hπ
        exact exp_ne_zero hπ.symm
      have hπinv : v π⁻¹ = exp 1 := by
        rw [map_inv₀, hπ, exp_neg, inv_inv]
      obtain ⟨C, hC⟩ := ih (n - 3) (by omega) (π⁻¹ * A) (π⁻¹ ^ 3 * B) (π⁻¹ ^ 2 * x)
        (by
          rw [map_mul, hπinv]
          refine (mul_le_mul_right hA' _).trans (le_of_eq ?_)
          rw [← exp_add]
          norm_num)
        (by
          rw [map_mul, map_pow, hπinv, hB, ← exp_nsmul, ← exp_add]
          congr 1
          push_cast [Nat.cast_sub hn3]
          ring)
        (mul_ne_zero (pow_ne_zero _ (inv_ne_zero hπ0)) hx0)
        (by linear_combination π⁻¹ ^ 6 * hg)
      refine ⟨C * ⟨Units.mk0 π hπ0, 0, 0, 0⟩, ?_⟩
      rw [mul_smul, normalForm_scale]
      exact hC

end Descent

end AbcAdaptation.Reference.Iut
