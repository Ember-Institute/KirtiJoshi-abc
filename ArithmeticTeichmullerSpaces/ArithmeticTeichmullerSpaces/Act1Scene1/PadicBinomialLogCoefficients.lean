import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.SpecificLimits.Normed

/-!
source-id: JT-SCENE1-PADIC-BINOMIAL-LOG-COEFFICIENTS
source: Joshi II multiplicative Tate logarithm; Iwasawa's normalized
p-power difference quotients and their rational binomial coefficients.
fidelity: identifies normalized binomial coefficients with polynomial
values, and proves their p-power sequence converges p-adically to the
standard log coefficients. Original proofs; no reference code copied.
boundary: Scene1/Derived; summation and actual period-ring consumers
are separate from this coefficient computation.
-/

namespace JoshiTeich.Act1Scene1.PadicBinomialLogCoefficients

open scoped Topology
noncomputable section

def coefficient (F : Type*) [Field F] (m n : ℕ) : F :=
  if n = 0 then 0 else (m.choose n : F) / (m : F)

theorem coefficient_succ_eq (F : Type*) [Field F] [CharZero F]
    (m n : ℕ) (hm : m ≠ 0) :
    coefficient F m (n + 1) = ((m - 1).choose n : F) / (n + 1 : ℕ) := by
  rw [coefficient, if_neg (Nat.succ_ne_zero n)]
  apply (div_eq_div_iff (Nat.cast_ne_zero.mpr hm)
    (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))).mpr
  have h := congrArg (fun k : ℕ => (k : F)) (Nat.add_one_mul_choose_eq (m - 1) n)
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)] at h
  simpa only [Nat.cast_mul, mul_comm] using h.symm

theorem coefficient_succ_polynomial (F : Type*) [Field F] [CharZero F]
    (m n : ℕ) (hm : m ≠ 0) :
    coefficient F m (n + 1) =
      (descPochhammer F n).eval ((m : F) - 1) / ((n + 1).factorial : F) := by
  rw [coefficient_succ_eq F m n hm, Nat.cast_choose_eq_descPochhammer_div,
    Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hm), Nat.cast_one,
    Nat.factorial_succ, Nat.cast_mul, div_div]
  congr 1
  exact mul_comm _ _

theorem descPochhammer_eval_neg_one (F : Type*) [Field F] (n : ℕ) :
    (descPochhammer F n).eval (-1) = (-1 : F) ^ n * (n.factorial : F) := by
  induction n with
  | zero => simp [descPochhammer_zero]
  | succ n ih =>
    rw [descPochhammer_succ_eval, ih, pow_succ, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring

theorem polynomial_limit_value (F : Type*) [Field F] [CharZero F] (n : ℕ) :
    (descPochhammer F n).eval (-1) / ((n + 1).factorial : F) =
      (-1 : F) ^ (n + 2) * (n + 1 : F)⁻¹ := by
  rw [descPochhammer_eval_neg_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    pow_add, neg_one_sq, mul_one]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)]

theorem tendsto_coefficient (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Filter.Tendsto (fun k : ℕ => coefficient (Padic p) (p ^ k) n) Filter.atTop
      (𝓝 (if n = 0 then 0 else (-1 : Padic p) ^ (n + 1) * (n : Padic p)⁻¹)) := by
  cases n with
  | zero => simpa only [coefficient, ite_true] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : Padic p)) Filter.atTop (𝓝 0))
  | succ n =>
    have hp : Filter.Tendsto (fun k : ℕ => (p : Padic p) ^ k) Filter.atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (Padic.norm_p_lt_one (p := p))
    have h := (((descPochhammer (Padic p) n).continuous.tendsto (-1)).comp
      (by simpa only [zero_sub] using hp.sub_const 1)).div_const ((n + 1).factorial : Padic p)
    have hcoeff (k : ℕ) := coefficient_succ_polynomial (Padic p) (p ^ k) n
      (pow_ne_zero k (Fact.out : p.Prime).ne_zero)
    simpa only [if_neg (Nat.succ_ne_zero n), hcoeff, Nat.cast_pow, polynomial_limit_value,
      Nat.cast_add, Nat.cast_one, Function.comp_def, Nat.add_assoc] using h

end
end JoshiTeich.Act1Scene1.PadicBinomialLogCoefficients
