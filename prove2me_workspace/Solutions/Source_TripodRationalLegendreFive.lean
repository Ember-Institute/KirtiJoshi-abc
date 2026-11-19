import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FieldLegendreFacts
import Definitions.Def_TripodCanonicalHighHeightInputs
import Theorems.Thm_AbcAdaptation_Tripod_legendre_isElliptic
import Mathlib.NumberTheory.Padics.PadicNorm
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open WeierstrassCurve

/-- The rational Legendre parameter of the family approaching `1/2`. -/
def rationalLegendreFiveParam (m : ℕ) : ℚ := 5 ^ m / (2 * 5 ^ m + 1)

theorem rationalLegendreFiveParam_bounds (m : ℕ) :
    (1 / 3 : ℚ) ≤ rationalLegendreFiveParam m ∧
      rationalLegendreFiveParam m < 1 / 2 := by
  have ha : (1 : ℚ) ≤ 5 ^ m := one_le_pow₀ (by norm_num)
  have hb : (0 : ℚ) < 2 * 5 ^ m + 1 := by linarith
  unfold rationalLegendreFiveParam
  constructor
  · rw [le_div_iff₀ hb]
    linarith
  · rw [div_lt_iff₀ hb]
    linarith

theorem rationalLegendreFive_isElliptic (m : ℕ) :
    (legendre (rationalLegendreFiveParam m)).IsElliptic := by
  obtain ⟨hlo, hhi⟩ := rationalLegendreFiveParam_bounds m
  apply legendre_isElliptic
  · exact ne_of_gt (by linarith)
  · exact ne_of_lt (by linarith)

local instance rationalLegendreFivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private theorem padicValRat_five_natCast_eq_zero {a : ℕ} (h : ¬ 5 ∣ a) :
    padicValRat 5 (a : ℚ) = 0 := by
  rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd h, Nat.cast_zero]

theorem padicValRat_rationalLegendreFiveParam (m : ℕ) (hm : 0 < m) :
    padicValRat 5 (rationalLegendreFiveParam m) = m := by
  let a : ℚ := 5 ^ m
  have ha : 0 < a := pow_pos (by norm_num) _
  have hb : 0 < 2 * a + 1 := by linarith
  have h2 : padicValRat 5 (2 : ℚ) = 0 :=
    padicValRat_five_natCast_eq_zero (a := 2) (by decide)
  have hv5 : padicValRat 5 (5 : ℚ) = 1 :=
    padicValRat.self (p := 5) (by norm_num)
  have hva : padicValRat 5 a = m := by
    dsimp only [a]
    rw [padicValRat.pow, hv5, mul_one]
  have h2a : 2 * a ≠ 0 := mul_ne_zero (by norm_num) ha.ne'
  have hv2a : padicValRat 5 (2 * a) = m := by
    rw [padicValRat.mul (p := 5) (by norm_num) ha.ne', h2, hva, zero_add]
  have hvb : padicValRat 5 (2 * a + 1) = 0 := by
    rw [add_comm (2 * a) 1]
    have hsum : 1 + 2 * a ≠ 0 := by
      rw [add_comm (1 : ℚ)]
      exact hb.ne'
    have hvlt : padicValRat 5 (1 : ℚ) < padicValRat 5 (2 * a) := by
      rw [padicValRat.one, hv2a]
      exact_mod_cast hm
    rw [padicValRat.add_eq_of_lt hsum one_ne_zero h2a hvlt, padicValRat.one]
  change padicValRat 5 (a / (2 * a + 1)) = m
  rw [padicValRat.div (p := 5) ha.ne' hb.ne', hva, hvb, sub_zero]

/-- The rational `j`-invariant has a pole of order `2m` at `5`. -/
theorem padicValRat_legendreJ_rationalLegendreFiveParam (m : ℕ) (hm : 0 < m) :
    padicValRat 5 (legendreJ (rationalLegendreFiveParam m)) = -(2 * (m : ℤ)) := by
  obtain ⟨hlo, hhi⟩ := rationalLegendreFiveParam_bounds m
  let x := rationalLegendreFiveParam m
  change (1 / 3 : ℚ) ≤ x at hlo
  change x < (1 / 2 : ℚ) at hhi
  have hx0 : x ≠ 0 := ne_of_gt (by linarith)
  have hx1 : x - 1 ≠ 0 := ne_of_lt (by linarith)
  have hvx : padicValRat 5 x = m := padicValRat_rationalLegendreFiveParam m hm
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  have hvx1 : padicValRat 5 (x - 1) = 0 := by
    have hsum : (1 : ℚ) + -x ≠ 0 := ne_of_gt (by linarith)
    have hvlt : padicValRat 5 (1 : ℚ) < padicValRat 5 (-x) := by
      rw [padicValRat.one, padicValRat.neg, hvx]
      exact hmZ
    rw [show x - 1 = -(1 + -x) by ring, padicValRat.neg,
      padicValRat.add_eq_of_lt hsum one_ne_zero (neg_ne_zero.mpr hx0) hvlt, padicValRat.one]
  have hc : x ^ 2 - x + 1 ≠ 0 := by
    rw [show x ^ 2 - x + 1 = (x - 1 / 2) ^ 2 + 3 / 4 by ring]
    exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) (by norm_num))
  have hvc : padicValRat 5 (x ^ 2 - x + 1) = 0 := by
    have hpoly : x ^ 2 - x + 1 = 1 + x * (x - 1) := by ring
    have hsum : 1 + x * (x - 1) ≠ 0 := hpoly ▸ hc
    have hvlt : padicValRat 5 (1 : ℚ) < padicValRat 5 (x * (x - 1)) := by
      rw [padicValRat.one, padicValRat.mul (p := 5) hx0 hx1, hvx, hvx1, add_zero]
      exact hmZ
    rw [hpoly, padicValRat.add_eq_of_lt hsum one_ne_zero (mul_ne_zero hx0 hx1) hvlt,
      padicValRat.one]
  have hv256 : padicValRat 5 (256 : ℚ) = 0 :=
    padicValRat_five_natCast_eq_zero (a := 256) (by decide)
  have h256 : (256 : ℚ) ≠ 0 := by norm_num
  change padicValRat 5 (legendreJ x) = _
  rw [legendreJ, padicValRat.div (p := 5) (mul_ne_zero h256 (pow_ne_zero 3 hc))
      (mul_ne_zero (pow_ne_zero 2 hx0) (pow_ne_zero 2 hx1)),
    padicValRat.mul (p := 5) h256 (pow_ne_zero 3 hc),
    padicValRat.mul (p := 5) (pow_ne_zero 2 hx0) (pow_ne_zero 2 hx1)]
  simp only [padicValRat.pow, hv256, hvc, hvx, hvx1]
  ring

theorem padicNorm_legendreJ_rationalLegendreFiveParam (m : ℕ) (hm : 0 < m) :
    padicNorm 5 (legendreJ (rationalLegendreFiveParam m)) = (5 : ℚ) ^ (2 * m) := by
  have hv := padicValRat_legendreJ_rationalLegendreFiveParam m hm
  have hj : legendreJ (rationalLegendreFiveParam m) ≠ 0 := by
    intro hj
    rw [hj, padicValRat.zero] at hv
    have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
    omega
  rw [padicNorm.eq_zpow_of_nonzero hj, hv, neg_neg,
    show 2 * (m : ℤ) = ((2 * m : ℕ) : ℤ) by simp, zpow_natCast, Nat.cast_ofNat]

theorem padicValRat_j_rationalLegendreFive (m : ℕ) (hm : 0 < m) :
    letI := rationalLegendreFive_isElliptic m
    padicValRat 5 (legendre (rationalLegendreFiveParam m)).j = -(2 * (m : ℤ)) := by
  let _ : (legendre (rationalLegendreFiveParam m)).IsElliptic := rationalLegendreFive_isElliptic m
  change padicValRat 5 (legendre (rationalLegendreFiveParam m)).j = _
  rw [legendre_j]
  exact padicValRat_legendreJ_rationalLegendreFiveParam m hm

end AbcAdaptation.Tripod
