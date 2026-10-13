/-
original-path: `refer/iut/Iut/Concrete/LocalConstruct/PadicLog.lean`
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: `bc1c6e6c7ac4bcf0c363b9b1bbe9b6d7bc35bf9c`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project LICENSE)
modification: selected integer-norm, series convergence and small-ball remainder
proofs; independent namespace and exact imports. Homomorphism, surjectivity,
compactness and tensor-packet construction are not copied.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
source-id: JT-SCENE1-LOCAL-PADIC-LOG-WITNESS
fidelity: constructs the ordinary local p-adic logarithm and proves its
norm identity on the ball of radius norm(2p). This does not construct a
Bloch-Kato class, a different untilt or a theta hull.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalPadicLog

open Filter Topology
open scoped Valued

universe u
noncomputable section

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]

section NatNorm

variable {p : ℕ}

/-- An integer prime to the residue characteristic has norm `1`. -/
theorem norm_natCast_eq_one_of_not_dvd (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {m : ℕ}
    (hm : ¬ p ∣ m) : ‖(m : k)‖ = 1 := by
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  have hb := Nat.gcd_eq_gcd_ab p m
  rw [hcop.gcd_eq_one] at hb
  have hk : (1 : k) = (p : k) * ((Nat.gcdA p m : ℤ) : k) + (m : k) * ((Nat.gcdB p m : ℤ) : k) := by
    have := congrArg (Int.cast : ℤ → k) hb
    push_cast at this
    exact this
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one k m) ?_
  by_contra! h
  have h1 : ‖(1 : k)‖ ≤ max ‖(p : k) * ((Nat.gcdA p m : ℤ) : k)‖
      ‖(m : k) * ((Nat.gcdB p m : ℤ) : k)‖ := by
    conv_lhs => rw [hk]
    exact IsUltrametricDist.norm_add_le_max _ _
  rw [norm_one, norm_mul, norm_mul] at h1
  have hA := IsUltrametricDist.norm_intCast_le_one k (Nat.gcdA p m)
  have hB := IsUltrametricDist.norm_intCast_le_one k (Nat.gcdB p m)
  have h2 : ‖(p : k)‖ * ‖((Nat.gcdA p m : ℤ) : k)‖ < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hpk hA
  have h3 : ‖(m : k)‖ * ‖((Nat.gcdB p m : ℤ) : k)‖ < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h hB
  exact absurd h1 (not_le.2 (max_lt h2 h3))

/-- `‖m‖ = ‖p‖ ^ v_p(m)` for a nonzero integer `m`. -/
theorem norm_natCast_eq_pow (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {m : ℕ} (hm : m ≠ 0) :
    ‖(m : k)‖ = ‖(p : k)‖ ^ m.factorization p := by
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self m p]
  rw [Nat.cast_mul, norm_mul, Nat.cast_pow, norm_pow,
    norm_natCast_eq_one_of_not_dvd hp hpk (Nat.not_dvd_ordCompl hp hm), mul_one]

/-- `v_p(m) < m` for `m ≠ 0`. -/
theorem factorization_lt_self (hp : p.Prime) {m : ℕ} (hm : m ≠ 0) : m.factorization p < m :=
  (Nat.lt_pow_self hp.one_lt).trans_le (Nat.ordProj_le p hm)

/-- The polynomial bound `‖m‖⁻¹ ≤ m ^ N` on the inverse norms of integers, for a suitable `N`
(any `N` with `‖p‖⁻¹ ≤ p ^ N`). -/
theorem exists_norm_natCast_inv_le [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) :
    ∃ N : ℕ, ∀ m : ℕ, ‖(m : k)‖⁻¹ ≤ (m : ℝ) ^ N := by
  have hp0 : (0 : ℝ) < ‖(p : k)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.ne_zero)
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (‖(p : k)‖⁻¹)
    (by exact_mod_cast hp.one_lt : (1 : ℝ) < p)
  refine ⟨N, fun m => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rw [norm_natCast_eq_pow hp hpk hm, ← inv_pow]
  calc (‖(p : k)‖⁻¹) ^ (m.factorization p) ≤ ((p : ℝ) ^ N) ^ (m.factorization p) :=
        pow_le_pow_left₀ (by positivity) hN.le _
    _ = ((p : ℝ) ^ m.factorization p) ^ N := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ (m : ℝ) ^ N :=
        pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.ordProj_le p hm) _

/-- `‖2‖ ≤ 1`. -/
theorem norm_two_le_one : ‖(2 : k)‖ ≤ 1 := by
  simpa using IsUltrametricDist.norm_natCast_le_one k 2

/-- `‖2‖ = 1` when `p` is odd. -/
theorem norm_two_eq_one (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) (hodd : Odd p) : ‖(2 : k)‖ = 1 := by
  have : ¬ p ∣ 2 := fun h => by
    have := (Nat.le_of_dvd two_pos h).antisymm hp.two_le
    subst this
    exact absurd hodd (by decide)
  simpa using norm_natCast_eq_one_of_not_dvd hp hpk this

/-- `‖2p‖ < 1`. -/
theorem norm_two_mul_lt_one (hpk : ‖(p : k)‖ < 1) : ‖2 * (p : k)‖ < 1 := by
  rw [norm_mul]
  exact mul_lt_one_of_nonneg_of_lt_one_right norm_two_le_one (norm_nonneg _) hpk

/-- The key numeric estimate for the contraction argument: `‖2p‖ ^ (m - 1) ≤ ‖p‖ ‖m‖` for
`m ≥ 2`. -/
theorem norm_two_mul_pow_le (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {m : ℕ} (hm : 2 ≤ m) :
    ‖2 * (p : k)‖ ^ (m - 1) ≤ ‖(p : k)‖ * ‖(m : k)‖ := by
  have hm0 : m ≠ 0 := by omega
  rw [norm_natCast_eq_pow hp hpk hm0, ← pow_succ']
  set v := m.factorization p with hv
  have hpv : p ^ v ≤ m := Nat.ordProj_le p hm0
  have hp1 : ‖(p : k)‖ ≤ 1 := hpk.le
  rcases eq_or_ne p 2 with rfl | h2
  · -- `p = 2`: `‖4‖ ^ (m-1) = ‖2‖ ^ (2 (m - 1)) ≤ ‖2‖ ^ (v + 1)` since `v + 1 ≤ 2 (m - 1)`.
    have : (2 : k) * ((2 : ℕ) : k) = ((2 : ℕ) : k) ^ 2 := by push_cast; ring
    rw [this, norm_pow, ← pow_mul]
    refine pow_le_pow_of_le_one (norm_nonneg _) hp1 ?_
    have : v < m := factorization_lt_self hp hm0
    omega
  · -- `p` odd: `‖2p‖ ^ (m-1) ≤ ‖p‖ ^ (m-1) ≤ ‖p‖ ^ (v + 1)` since `v + 1 ≤ m - 1`.
    have h2p : ‖2 * (p : k)‖ ≤ ‖(p : k)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) norm_two_le_one
    refine (pow_le_pow_left₀ (norm_nonneg _) h2p _).trans
      (pow_le_pow_of_le_one (norm_nonneg _) hp1 ?_)
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    rcases Nat.eq_zero_or_pos v with hv0 | hv0
    · omega
    · -- `v + 2 ≤ 2 v + 1 ≤ 3 ^ v ≤ p ^ v ≤ m`
      have h3 : 1 + v * 2 ≤ 3 ^ v := by
        have := one_add_mul_le_pow (a := (2 : ℤ)) (by norm_num) v
        exact_mod_cast this
      have h4 : 3 ^ v ≤ p ^ v := Nat.pow_le_pow_left hp3 v
      omega

end NatNorm

section Series

variable {p : ℕ}

/-- The `n`-th term `(-1)^n (x - 1)^(n+1) / (n+1)` of the logarithm series at `x`. -/
def logTerm (x : k) (n : ℕ) : k := (-1) ^ n * (x - 1) ^ (n + 1) / (n + 1)

/-- The `p`-adic logarithm `log x = ∑ (-1)^n (x - 1)^(n+1)/(n+1)`; the series converges for
`‖x - 1‖ < 1` (and the definition is only meaningful there). -/
def padicLog (x : k) : k := ∑' n, logTerm x n

omit [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] in
@[simp] theorem logTerm_one (n : ℕ) : logTerm (1 : k) n = 0 := by simp [logTerm]

omit [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] in
@[simp] theorem padicLog_one : padicLog (1 : k) = 0 := by simp [padicLog]

omit [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] in
theorem logTerm_zero (x : k) : logTerm x 0 = x - 1 := by simp [logTerm]

theorem norm_logTerm [CharZero k] (x : k) (n : ℕ) :
    ‖logTerm x n‖ = ‖x - 1‖ ^ (n + 1) * ‖((n + 1 : ℕ) : k)‖⁻¹ := by
  unfold logTerm
  rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow,
    div_eq_mul_inv]
  push_cast
  rfl

theorem norm_logTerm_le [CharZero k] {N : ℕ} (hN : ∀ m : ℕ, ‖(m : k)‖⁻¹ ≤ (m : ℝ) ^ N) (x : k)
    (n : ℕ) : ‖logTerm x n‖ ≤ ((n + 1 : ℕ) : ℝ) ^ N * ‖x - 1‖ ^ (n + 1) := by
  rw [norm_logTerm, mul_comm]
  exact mul_le_mul_of_nonneg_right (hN _) (by positivity)

/-- The terms of the logarithm series tend to `0` for `‖x - 1‖ < 1`. -/
theorem tendsto_logTerm [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {x : k}
    (hx : ‖x - 1‖ < 1) : Tendsto (logTerm x) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := exists_norm_natCast_inv_le hp hpk
  have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one N
    (abs_lt.2 ⟨by linarith [norm_nonneg (x - 1)], hx⟩)
  have h' := h.comp (tendsto_add_atTop_nat 1)
  exact squeeze_zero_norm (fun n => norm_logTerm_le hN x n) h'

/-- The ultrametric bound `‖log x‖ ≤ C` from a uniform bound on the terms (no summability
needed). -/
theorem norm_padicLog_le_of_forall_le {x : k} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n, ‖logTerm x n‖ ≤ C) : ‖padicLog x‖ ≤ C :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC h

/-- For `‖x - 1‖ ≤ ‖p‖` every term of the series has norm `≤ ‖p‖`. -/
theorem norm_logTerm_le_norm_p [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {x : k}
    (hx : ‖x - 1‖ ≤ ‖(p : k)‖) (n : ℕ) : ‖logTerm x n‖ ≤ ‖(p : k)‖ := by
  have hp0 : (0 : ℝ) < ‖(p : k)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.ne_zero)
  rw [norm_logTerm, norm_natCast_eq_pow hp hpk (Nat.succ_ne_zero n)]
  set v := (n + 1).factorization p
  have hv : v < n + 1 := factorization_lt_self hp (Nat.succ_ne_zero n)
  calc ‖x - 1‖ ^ (n + 1) * (‖(p : k)‖ ^ v)⁻¹
      ≤ ‖(p : k)‖ ^ (n + 1) * (‖(p : k)‖ ^ v)⁻¹ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hx _) (by positivity)
    _ = ‖(p : k)‖ ^ (n + 1 - v) := by
        rw [← pow_sub₀ _ hp0.ne' hv.le]
    _ ≤ ‖(p : k)‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) hpk.le (by omega)
    _ = ‖(p : k)‖ := pow_one _

/-- For `‖x - 1‖ ≤ ‖p‖` one has `‖log x‖ ≤ ‖p‖`. -/
theorem norm_padicLog_le_norm_p [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {x : k}
    (hx : ‖x - 1‖ ≤ ‖(p : k)‖) : ‖padicLog x‖ ≤ ‖(p : k)‖ :=
  norm_padicLog_le_of_forall_le (norm_nonneg _) (norm_logTerm_le_norm_p hp hpk hx)

variable [CompleteSpace k]

/-- The logarithm series is summable for `‖x - 1‖ < 1`. -/
theorem summable_logTerm [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {x : k}
    (hx : ‖x - 1‖ < 1) : Summable (logTerm x) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (Nat.cofinite_eq_atTop ▸ tendsto_logTerm hp hpk hx)

theorem hasSum_padicLog [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {x : k}
    (hx : ‖x - 1‖ < 1) : HasSum (logTerm x) (padicLog x) :=
  (summable_logTerm hp hpk hx).hasSum

end Series

section Surjective

variable {p : ℕ}

/-- The remainder `log (1 + a) - a = ∑_{n ≥ 1} (-1)^n a^(n+1)/(n+1)`. -/
def logRem (a : k) : k := ∑' n, logTerm (1 + a) (n + 1)

omit [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] in
@[simp] theorem logRem_zero : logRem (0 : k) = 0 := by simp [logRem]

variable [CompleteSpace k]

theorem padicLog_one_add [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {a : k}
    (ha : ‖a‖ < 1) : padicLog (1 + a) = a + logRem a := by
  unfold padicLog logRem
  rw [(summable_logTerm hp hpk (by simpa using ha)).tsum_eq_zero_add, logTerm_zero,
    add_sub_cancel_left]

omit [CompleteSpace k] in
/-- The termwise Lipschitz estimate for the remainder on the ball of radius `‖2p‖`. -/
theorem norm_logTerm_sub_le [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {a b : k}
    (ha : ‖a‖ ≤ ‖2 * (p : k)‖) (hb : ‖b‖ ≤ ‖2 * (p : k)‖) (n : ℕ) :
    ‖logTerm (1 + a) (n + 1) - logTerm (1 + b) (n + 1)‖ ≤ ‖(p : k)‖ * ‖a - b‖ := by
  have hmn : (0 : ℝ) < ‖((n + 2 : ℕ) : k)‖ :=
    norm_pos_iff.2 (Nat.cast_ne_zero.2 (Nat.succ_ne_zero _))
  have key : logTerm (1 + a) (n + 1) - logTerm (1 + b) (n + 1) = (-1) ^ (n + 1) *
      ((∑ i ∈ Finset.range (n + 2), a ^ i * b ^ (n + 2 - 1 - i)) * (a - b)) /
        ((n + 2 : ℕ) : k) := by
    unfold logTerm
    rw [geom_sum₂_mul]
    push_cast
    ring
  rw [key, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_mul,
    div_le_iff₀ hmn]
  have hsum : ‖∑ i ∈ Finset.range (n + 2), a ^ i * b ^ (n + 2 - 1 - i)‖ ≤
      ‖2 * (p : k)‖ ^ (n + 2 - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow, norm_pow]
    calc ‖a‖ ^ i * ‖b‖ ^ (n + 2 - 1 - i)
        ≤ ‖2 * (p : k)‖ ^ i * ‖2 * (p : k)‖ ^ (n + 2 - 1 - i) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ha _)
            (pow_le_pow_left₀ (norm_nonneg _) hb _) (by positivity) (by positivity)
      _ = ‖2 * (p : k)‖ ^ (n + 2 - 1) := by
          rw [← pow_add]
          congr 1
          omega
  calc ‖∑ i ∈ Finset.range (n + 2), a ^ i * b ^ (n + 2 - 1 - i)‖ * ‖a - b‖
      ≤ ‖2 * (p : k)‖ ^ (n + 2 - 1) * ‖a - b‖ := mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
    _ ≤ (‖(p : k)‖ * ‖((n + 2 : ℕ) : k)‖) * ‖a - b‖ :=
        mul_le_mul_of_nonneg_right (norm_two_mul_pow_le hp hpk (by omega)) (norm_nonneg _)
    _ = ‖(p : k)‖ * ‖a - b‖ * ‖((n + 2 : ℕ) : k)‖ := by ring

/-- The remainder `a ↦ log (1 + a) - a` is a contraction with contraction factor `‖p‖` on the ball of
radius `‖2p‖`. -/
theorem norm_logRem_sub_le [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {a b : k}
    (ha : ‖a‖ ≤ ‖2 * (p : k)‖) (hb : ‖b‖ ≤ ‖2 * (p : k)‖) :
    ‖logRem a - logRem b‖ ≤ ‖(p : k)‖ * ‖a - b‖ := by
  have h2 := norm_two_mul_lt_one (k := k) hpk
  have ha' : ‖(1 + a) - 1‖ < 1 := by simpa using ha.trans_lt h2
  have hb' : ‖(1 + b) - 1‖ < 1 := by simpa using hb.trans_lt h2
  unfold logRem
  rw [← Summable.tsum_sub ((summable_nat_add_iff 1).2 (summable_logTerm hp hpk ha'))
    ((summable_nat_add_iff 1).2 (summable_logTerm hp hpk hb'))]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity)
    (norm_logTerm_sub_le hp hpk ha hb)

theorem norm_logRem_le [CharZero k] (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {a : k}
    (ha : ‖a‖ ≤ ‖2 * (p : k)‖) : ‖logRem a‖ ≤ ‖(p : k)‖ * ‖a‖ := by
  simpa using norm_logRem_sub_le hp hpk ha (b := 0) (by simp)

end Surjective

section Witness

variable [CharZero k] [CompleteSpace k] {p : ℕ}

/-- The convergent logarithm has the norm of its linear term on the small ball. -/
theorem norm_padicLog_one_add (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
    {a : k} (ha : ‖a‖ ≤ ‖2 * (p : k)‖) : ‖padicLog (1 + a)‖ = ‖a‖ := by
  by_cases ha0 : a = 0
  · simp [ha0]
  · have h0 : 0 < ‖a‖ := norm_pos_iff.mpr ha0
    have hRem : ‖logRem a‖ < ‖a‖ :=
      (norm_logRem_le hp hpk ha).trans_lt (mul_lt_of_lt_one_left h0 hpk)
    rw [padicLog_one_add hp hpk (ha.trans_lt (norm_two_mul_lt_one hpk))]
    have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (x := a) (y := logRem a) hRem.ne'
    simpa [max_eq_left hRem.le] using h

/-- Normalize the local logarithm using the actual small-ball scaling element. -/
def normalizedLog (p : ℕ) (y : k) : k :=
  (2 * (p : k))⁻¹ * padicLog (1 + 2 * (p : k) * y)

/-- The log-shell as an image of the principal units under the normalized log. -/
def logShell (p : ℕ) : Set k :=
  {z | ∃ u : k, ‖u - 1‖ < 1 ∧ z = (2 * (p : k))⁻¹ * padicLog u}

theorem normalizedLog_mem_logShell (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
    {y : k} (hy : ‖y‖ ≤ 1) : normalizedLog p y ∈ logShell p := by
  refine ⟨1 + 2 * (p : k) * y, ?_, rfl⟩
  simp only [add_sub_cancel_left]
  rw [norm_mul]
  calc
    ‖2 * (p : k)‖ * ‖y‖ ≤ ‖2 * (p : k)‖ :=
      mul_le_of_le_one_right (norm_nonneg _) hy
    _ < 1 := norm_two_mul_lt_one hpk

theorem norm_normalizedLog (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
    {y : k} (hy : ‖y‖ ≤ 1) : ‖normalizedLog p y‖ = ‖y‖ := by
  have h2p : 2 * (p : k) ≠ 0 := mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr hp.ne_zero)
  have ha : ‖2 * (p : k) * y‖ ≤ ‖2 * (p : k)‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hy
  rw [normalizedLog, norm_mul, norm_padicLog_one_add hp hpk ha,
    norm_mul, norm_inv, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h2p), one_mul]

end Witness
end
end JoshiTeich.Act1Scene1.LocalPadicLog
