/-
original-path: `refer/iut/Iut/Concrete/LocalConstruct/PadicLog.lean`
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: `bc1c6e6c7ac4bcf0c363b9b1bbe9b6d7bc35bf9c`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project LICENSE)
modification: selected the limit and homomorphism segment only; independent
namespace, exact imports and existing JoshiTeich logarithm definitions.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalPadicLog
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.LinearCombination

/-!
source-id: JT-SCENE1-LOCAL-PADIC-LOG-HOMOMORPHISM
source: Joshi III logarithm comparison (3226), with the local logarithm
homomorphism proof from the independent reference implementation.
fidelity: proves multiplication, powers, inverses and vanishing on roots of
unity for the already defined convergent ordinary p-adic logarithm. It does
not identify this logarithm with a Bloch--Kato logarithm.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalPadicLog
open Filter Topology
open scoped Valued
universe u
noncomputable section
variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]

section Limit
variable {p : ℕ}

omit [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] in
theorem pow_sub_one_div_eq_tsum [CharZero k] (x : k) {N : ℕ} (hN : N ≠ 0) :
    (x ^ N - 1) / N = ∑' n : ℕ, ((N - 1).choose n : k) / (n + 1) * (x - 1) ^ (n + 1) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hx : x = (x - 1) + 1 := by ring
  rw [tsum_eq_sum (s := Finset.range (M + 1)) (fun n hn => ?_)]
  · conv_lhs => rw [hx, add_pow, Finset.sum_range_succ']
    simp only [Nat.add_sub_cancel, one_pow, mul_one, pow_zero, Nat.choose_zero_right,
      Nat.cast_one, add_sub_cancel_right]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    have h : ((M : k) + 1) * (M.choose n : k) = ((M + 1).choose (n + 1) : k) * ((n : k) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq M n
    have hM : ((M : k) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero M
    have hn : ((n : k) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hc : ((M + 1).choose (n + 1) : k) / ((M : k) + 1) = (M.choose n : k) / ((n : k) + 1) := by
      rw [div_eq_div_iff hM hn]
      linear_combination -h
    push_cast
    rw [mul_div_assoc, hc]
    ring
  · rw [Finset.mem_range, not_lt] at hn
    rw [Nat.add_sub_cancel, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_div, zero_mul]

omit [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] in
theorem cast_choose_eq_descPochhammer_div [CharZero k] (N n : ℕ) :
    (N.choose n : k) = (descPochhammer k n).eval (N : k) / (n.factorial : k) := by
  rw [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  have h : (n.factorial : k) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  push_cast
  field_simp

omit [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] in
theorem descPochhammer_eval_neg_one (n : ℕ) :
    (descPochhammer k n).eval (-1 : k) = (-1) ^ n * (n.factorial : k) := by
  rw [descPochhammer_eval_eq_prod_range]
  have h : ∀ j ∈ Finset.range n, (-1 : k) - j = -((j : k) + 1) := fun j _ => by ring
  rw [Finset.prod_congr rfl h, Finset.prod_neg, Finset.card_range]
  congr 1
  rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod]
  simp

theorem norm_mul_sub_one_lt {x y : k} (hx : ‖x - 1‖ < 1) (hy : ‖y - 1‖ < 1) :
    ‖x * y - 1‖ < 1 := by
  have h : x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1) := by ring
  rw [h]
  calc ‖(x - 1) * (y - 1) + (x - 1) + (y - 1)‖
      ≤ max (max ‖(x - 1) * (y - 1)‖ ‖x - 1‖) ‖y - 1‖ :=
        (IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le_max_right _ (IsUltrametricDist.norm_add_le_max _ _))
    _ < 1 := by
        rw [norm_mul]
        exact max_lt (max_lt (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hx hy.le) hx) hy

theorem norm_eq_one_of_norm_sub_one_lt {x : k} (hx : ‖x - 1‖ < 1) : ‖x‖ = 1 := by
  have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := x - 1) (y := 1)
    (by rw [norm_one]; exact hx.ne)
  rw [sub_add_cancel, norm_one, max_eq_right hx.le] at h
  exact h

theorem ne_zero_of_norm_sub_one_lt {x : k} (hx : ‖x - 1‖ < 1) : x ≠ 0 := by
  rintro rfl
  simp at hx

theorem norm_inv_sub_one_lt {x : k} (hx : ‖x - 1‖ < 1) : ‖x⁻¹ - 1‖ < 1 := by
  have hx0 : x ≠ 0 := ne_zero_of_norm_sub_one_lt hx
  have h : x⁻¹ - 1 = -(x - 1) * x⁻¹ := by rw [neg_sub, sub_mul, one_mul, mul_inv_cancel₀ hx0]
  rw [h, norm_mul, norm_neg, norm_inv, norm_eq_one_of_norm_sub_one_lt hx, inv_one, mul_one]
  exact hx

theorem norm_pow_sub_one_lt {x : k} (hx : ‖x - 1‖ < 1) (n : ℕ) : ‖x ^ n - 1‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; exact norm_mul_sub_one_lt ih hx

variable [CompleteSpace k]

theorem tendsto_pow_sub_one_div [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {x : k}
    (hx : ‖x - 1‖ < 1) :
    Tendsto (fun m : ℕ => (x ^ (p ^ m) - 1) / ((p : k) ^ m)) atTop (𝓝 (padicLog x)) := by
  obtain ⟨N, hN⟩ := exists_norm_natCast_inv_le hp hpk
  have heq : ∀ m : ℕ, (x ^ (p ^ m) - 1) / ((p : k) ^ m) =
      ∑' n : ℕ, ((p ^ m - 1).choose n : k) / (n + 1) * (x - 1) ^ (n + 1) := fun m => by
    have h := pow_sub_one_div_eq_tsum x (N := p ^ m) (pow_ne_zero _ hp.ne_zero)
    rw [Nat.cast_pow] at h
    exact h
  refine (Tendsto.congr (fun m => (heq m).symm)) ?_
  unfold padicLog
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun n => ((n + 1 : ℕ) : ℝ) ^ N * ‖x - 1‖ ^ (n + 1)) ?_ ?_
    (Eventually.of_forall fun m n => ?_)
  · refine (summable_nat_add_iff 1).2
      (summable_pow_mul_geometric_of_norm_lt_one N (r := ‖x - 1‖) ?_)
    rwa [Real.norm_of_nonneg (norm_nonneg _)]
  · intro n
    have hlim : Tendsto (fun m : ℕ => ((p ^ m - 1 : ℕ) : k)) atTop (𝓝 (-1)) := by
      have h : ∀ m, ((p ^ m - 1 : ℕ) : k) = (p : k) ^ m - 1 := fun m => by
        rw [Nat.cast_sub (Nat.one_le_pow _ _ hp.pos), Nat.cast_pow, Nat.cast_one]
      simp_rw [h]
      simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hpk).sub_const 1
    have h1 := ((descPochhammer k n).continuous.tendsto (-1 : k)).comp hlim
    rw [descPochhammer_eval_neg_one] at h1
    have h2 := ((h1.div_const (n.factorial : k)).div_const ((n : k) + 1)).mul_const
      ((x - 1) ^ (n + 1))
    convert h2 using 1
    · funext m
      simp only [Function.comp]
      rw [cast_choose_eq_descPochhammer_div]
    · have h : (n.factorial : k) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
      unfold logTerm
      field_simp
  · rw [norm_mul, norm_div, norm_pow]
    have hC : ‖((p ^ m - 1).choose n : k)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one k _
    have hn : ‖(n : k) + 1‖⁻¹ ≤ ((n : ℝ) + 1) ^ N := by
      have h := hN (n + 1)
      push_cast at h
      exact h
    push_cast
    calc ‖((p ^ m - 1).choose n : k)‖ / ‖(n : k) + 1‖ * ‖x - 1‖ ^ (n + 1)
        ≤ (1 * ((n : ℝ) + 1) ^ N) * ‖x - 1‖ ^ (n + 1) := by
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul hC hn (by positivity) zero_le_one) (by positivity)
      _ = ((n : ℝ) + 1) ^ N * ‖x - 1‖ ^ (n + 1) := by rw [one_mul]

theorem padicLog_mul [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {x y : k}
    (hx : ‖x - 1‖ < 1) (hy : ‖y - 1‖ < 1) : padicLog (x * y) = padicLog x + padicLog y := by
  have hp0 : (p : k) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have h1 := tendsto_pow_sub_one_div hp hpk hx
  have h2 := tendsto_pow_sub_one_div hp hpk hy
  have h3 := tendsto_pow_sub_one_div hp hpk (norm_mul_sub_one_lt hx hy)
  have hp0' : Tendsto (fun m : ℕ => (p : k) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hpk
  have h4 := (h1.add h2).add (hp0'.mul (h1.mul h2))
  rw [zero_mul, add_zero] at h4
  refine tendsto_nhds_unique h3 (h4.congr fun m => ?_)
  have hpow : (p : k) ^ m ≠ 0 := pow_ne_zero _ hp0
  field_simp
  ring

theorem padicLog_pow [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {x : k}
    (hx : ‖x - 1‖ < 1) (n : ℕ) : padicLog (x ^ n) = n * padicLog x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, padicLog_mul hp hpk (norm_pow_sub_one_lt hx n) hx, ih]
    push_cast
    ring

theorem padicLog_inv [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {x : k}
    (hx : ‖x - 1‖ < 1) : padicLog x⁻¹ = - padicLog x := by
  have h := padicLog_mul hp hpk hx (norm_inv_sub_one_lt hx)
  rw [mul_inv_cancel₀ (ne_zero_of_norm_sub_one_lt hx), padicLog_one] at h
  linear_combination -h

theorem padicLog_eq_zero_of_pow_eq_one [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
    {x : k} (hx : ‖x - 1‖ < 1) {n : ℕ} (hn : n ≠ 0) (h : x ^ n = 1) : padicLog x = 0 := by
  have hpow := padicLog_pow hp hpk hx n
  rw [h, padicLog_one] at hpow
  exact (mul_eq_zero.1 hpow.symm).resolve_left (Nat.cast_ne_zero.2 hn)

end Limit
end
end JoshiTeich.Act1Scene1.LocalPadicLog
