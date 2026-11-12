import ArithmeticTeichmullerSpaces.Act1Scene1.WittTeichmullerExpansion
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.ENNReal.Inv

/-!
source-id: JT-SCENE1-WITT-WEIGHTED-DIGITS
source: Joshi II `se:ff-rings` and the rho-weighted Teichmuller expansions
underlying the Frechet period ring in `pr:teichmuller-lift-A/B`.
fidelity: defines the extended nonnegative weighted supremum of the unique
Teichmuller digits of an actual Witt vector. Proves Teichmuller homogeneity,
prime-shift scaling, separation, and finiteness for uniformly bounded digits
at radii at most one. Original proofs; no reference code copied.
boundary: Scene1/Derived; this is a coefficient value on Witt vectors.
Addition/submultiplicativity, localization descent, topology and Frechet
completion remain to be proved before identifying a period-ring norm.
-/

namespace JoshiTeich.Act1Scene1.WittWeightedDigits

open WittTeichmullerExpansion
open scoped ENNReal
noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {F : Type*} [NormedField F] [CharP F p] [PerfectRing F p]

theorem digits_mul_prime_zero (x : WittVector p F) :
    digits p (x * (p : WittVector p F)) 0 = 0 := by
  simp [digits, WittVector.mul_charP_coeff_zero]

theorem digits_mul_prime_succ (x : WittVector p F) (n : ℕ) :
    digits p (x * (p : WittVector p F)) (n + 1) = digits p x n := by
  have hcoeff := fun (y : WittVector p F) =>
    (expands_iff_coeff p y (digits p y)).mp (expands_digits p y)
  have he : digits p (x * (p : WittVector p F)) (n + 1) ^ (p ^ (n + 1)) =
      digits p x n ^ (p ^ (n + 1)) := by
    rw [← hcoeff (x * (p : WittVector p F)) (n + 1), WittVector.mul_charP_coeff_succ,
      hcoeff x n, ← pow_mul, ← pow_succ]
  have hf : ((_root_.frobeniusEquiv F p) ^ (n + 1)) (digits p (x * (p : WittVector p F)) (n + 1)) =
      ((_root_.frobeniusEquiv F p) ^ (n + 1)) (digits p x n) := by
    simpa only [← iterateFrobeniusEquiv_eq_pow, iterateFrobeniusEquiv_def] using he
  exact ((_root_.frobeniusEquiv F p) ^ (n + 1)).injective hf

theorem digits_teichmuller_mul (r : F) (x : WittVector p F) (n : ℕ) :
    digits p (WittVector.teichmuller p r * x) n = r * digits p x n :=
  congrFun (digits_unique p _ _
    (expands_teichmuller_mul p r x (digits p x) (expands_digits p x))).symm n

theorem digits_teichmuller (r : F) (n : ℕ) :
    digits p (WittVector.teichmuller p r) n = if n = 0 then r else 0 := by
  cases n with
  | zero => simp [digits]
  | succ n => simp [digits, WittVector.teichmuller_coeff_pos p r _ (Nat.succ_pos n)]

def value (ρ : ℝ≥0∞) (x : WittVector p F) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal ‖digits p x n‖ * ρ ^ n

theorem term_le_value (ρ : ℝ≥0∞) (x : WittVector p F) (n : ℕ) :
    ENNReal.ofReal ‖digits p x n‖ * ρ ^ n ≤ value p ρ x :=
  le_iSup (fun n => ENNReal.ofReal ‖digits p x n‖ * ρ ^ n) n

theorem value_teichmuller (ρ : ℝ≥0∞) (r : F) :
    value p ρ (WittVector.teichmuller p r) = ENNReal.ofReal ‖r‖ := by
  unfold value
  rw [← sup_iSup_nat_succ]
  simp [digits_teichmuller]

theorem value_teichmuller_mul (ρ : ℝ≥0∞) (r : F) (x : WittVector p F) :
    value p ρ (WittVector.teichmuller p r * x) = ENNReal.ofReal ‖r‖ * value p ρ x := by
  unfold value
  rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro n
  rw [digits_teichmuller_mul, norm_mul, ENNReal.ofReal_mul (norm_nonneg _), mul_assoc]

theorem value_mul_prime (ρ : ℝ≥0∞) (x : WittVector p F) :
    value p ρ (x * (p : WittVector p F)) = ρ * value p ρ x := by
  unfold value
  rw [← sup_iSup_nat_succ]
  simp only [digits_mul_prime_zero, norm_zero, ENNReal.ofReal_zero, pow_zero, zero_mul,
    digits_mul_prime_succ]
  rw [max_eq_right (a := (0 : ℝ≥0∞)) (b :=
    ⨆ n : ℕ, ENNReal.ofReal ‖digits p x n‖ * ρ ^ (n + 1)) bot_le, ENNReal.mul_iSup]
  apply iSup_congr
  intro n
  rw [pow_succ]
  ac_rfl

theorem value_one (ρ : ℝ≥0∞) : value p ρ (1 : WittVector p F) = 1 := by
  rw [← (WittVector.teichmuller p).map_one, value_teichmuller]
  simp

theorem value_prime (ρ : ℝ≥0∞) : value p ρ (p : WittVector p F) = ρ := by
  have h := value_mul_prime p ρ (1 : WittVector p F)
  simpa only [one_mul, value_one, mul_one] using h

theorem value_mul_prime_pow (ρ : ℝ≥0∞) (x : WittVector p F) (m : ℕ) :
    value p ρ (x * (p : WittVector p F) ^ m) = ρ ^ m * value p ρ x := by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [pow_succ, ← mul_assoc, value_mul_prime, hm, pow_succ]
    ac_rfl

theorem value_zero (ρ : ℝ≥0∞) : value p ρ (0 : WittVector p F) = 0 := by
  rw [← WittVector.teichmuller_zero p, value_teichmuller]
  simp

theorem value_eq_zero_iff (ρ : ℝ≥0∞) (hρ : ρ ≠ 0) (x : WittVector p F) :
    value p ρ x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply WittVector.ext
    intro n
    have ht := term_le_value p ρ x n
    rw [hx] at ht
    have hd : digits p x n = 0 := by
      have he := (mul_eq_zero.mp (le_antisymm ht bot_le)).resolve_right (pow_ne_zero n hρ)
      exact norm_eq_zero.mp (ENNReal.ofReal_eq_zero.mp he |>.antisymm (norm_nonneg _))
    rw [(expands_iff_coeff p x (digits p x)).mp (expands_digits p x) n, hd,
      zero_pow (pow_ne_zero n (Fact.out : p.Prime).ne_zero), WittVector.zero_coeff]
  · rintro rfl
    exact value_zero p ρ

theorem value_le_of_bound (ρ : ℝ≥0∞) (hρ : ρ ≤ 1) (x : WittVector p F)
    (C : ℝ) (hC : ∀ n : ℕ, ‖digits p x n‖ ≤ C) :
    value p ρ x ≤ ENNReal.ofReal C := by
  apply iSup_le
  intro n
  simpa using mul_le_mul (ENNReal.ofReal_le_ofReal (hC n))
    (pow_le_one₀ bot_le hρ (n := n)) (bot_le : (0 : ℝ≥0∞) ≤ ρ ^ n)
    (bot_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal C)

theorem value_lt_top_of_bound (ρ : ℝ≥0∞) (hρ : ρ ≤ 1) (x : WittVector p F)
    (C : ℝ) (hC : ∀ n : ℕ, ‖digits p x n‖ ≤ C) : value p ρ x < ⊤ :=
  (value_le_of_bound p ρ hρ x C hC).trans_lt ENNReal.ofReal_lt_top

end
end JoshiTeich.Act1Scene1.WittWeightedDigits
