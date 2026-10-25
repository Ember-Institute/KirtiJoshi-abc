import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedDigitAddition

/-!
source-id: JT-SCENE1-WITT-WEIGHTED-DIGIT-MULTIPLICATION
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, the
rho-weighted Teichmuller expansions of the bounded period subring.
fidelity: bounds finite sums and products of actual Teichmuller monomials,
then uses truncated Witt ring homomorphisms to prove submultiplicativity
of the extended weighted digit value. No multiplication estimate is input.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; equality in the multiplicative estimate,
localization topology and completed Frechet B remain to be established.
-/

namespace JoshiTeich.Act1Scene1.WittWeightedDigitMultiplication

open WittTeichmullerExpansion WittWeightedDigits
open scoped ENNReal
noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {F : Type*} [NormedField F] [CharP F p] [PerfectRing F p]

theorem value_finset_sum_le (O : Subring F) (hO : ∀ a : F, a ∈ O ↔ ‖a‖ ≤ 1)
    (ρ : ℝ≥0∞) (hρ : ρ ≤ 1) {ι : Type*} (s : Finset ι) (f : ι → WittVector p F)
    (C : ℝ≥0∞) (hf : ∀ i ∈ s, value p ρ (f i) ≤ C) :
    value p ρ (∑ i ∈ s, f i) ≤ C := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
    intro hf
    rw [Finset.sum_empty, value_zero]
    exact bot_le
  | @insert i s hi ih =>
    intro hf
    rw [Finset.sum_insert hi]
    apply (WittWeightedDigitAddition.value_add_le_max p O hO ρ hρ _ _).trans
    exact max_le (hf i (Finset.mem_insert_self i s))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

omit [CharP F p] [PerfectRing F p] in
theorem monomial_mul (a b : F) (i j : ℕ) :
    (WittVector.teichmuller p a * (p : WittVector p F) ^ i) *
        (WittVector.teichmuller p b * (p : WittVector p F) ^ j) =
      WittVector.teichmuller p (a * b) * (p : WittVector p F) ^ (i + j) := by
  rw [map_mul, pow_add]
  ac_rfl

theorem value_monomial_product_le (ρ : ℝ≥0∞) (x y : WittVector p F) (i j : ℕ) :
    value p ρ ((WittVector.teichmuller p (digits p x i) * (p : WittVector p F) ^ i) *
      (WittVector.teichmuller p (digits p y j) * (p : WittVector p F) ^ j)) ≤
      value p ρ x * value p ρ y := by
  rw [monomial_mul, value_mul_prime_pow, value_teichmuller, norm_mul,
    ENNReal.ofReal_mul (norm_nonneg _), pow_add]
  calc
    _ = (ENNReal.ofReal ‖digits p x i‖ * ENNReal.ofReal ‖digits p y j‖) *
        (ρ ^ i * ρ ^ j) := mul_comm _ _
    _ = (ENNReal.ofReal ‖digits p x i‖ * ρ ^ i) *
        (ENNReal.ofReal ‖digits p y j‖ * ρ ^ j) := mul_mul_mul_comm _ _ _ _
    _ ≤ _ := mul_le_mul (term_le_value p ρ x i) (term_le_value p ρ y j) bot_le bot_le

theorem value_partialSum_product_le (O : Subring F)
    (hO : ∀ a : F, a ∈ O ↔ ‖a‖ ≤ 1) (ρ : ℝ≥0∞) (hρ : ρ ≤ 1)
    (x y : WittVector p F) (N : ℕ) :
    value p ρ (partialSum p (digits p x) N * partialSum p (digits p y) N) ≤
      value p ρ x * value p ρ y := by
  rw [partialSum, Finset.sum_mul]
  apply value_finset_sum_le p O hO ρ hρ
  intro i hi
  rw [partialSum, Finset.mul_sum]
  apply value_finset_sum_le p O hO ρ hρ
  intro j hj
  exact value_monomial_product_le p ρ x y i j

theorem truncate_partialSum_eq (x : WittVector p F) (N : ℕ) :
    (partialSum p (digits p x) N).truncate (N + 1) = x.truncate (N + 1) := by
  ext i
  rw [WittVector.coeff_truncate, WittVector.coeff_truncate,
    partialSum_coeff p _ N i.val (Nat.le_of_lt_succ i.isLt),
    (expands_iff_coeff p x (digits p x)).mp (expands_digits p x) i.val]

theorem value_mul_le (O : Subring F) (hO : ∀ a : F, a ∈ O ↔ ‖a‖ ≤ 1)
    (ρ : ℝ≥0∞) (hρ : ρ ≤ 1) (x y : WittVector p F) :
    value p ρ (x * y) ≤ value p ρ x * value p ρ y := by
  apply iSup_le
  intro n
  let a := partialSum p (digits p x) n
  let b := partialSum p (digits p y) n
  have ht : (a * b).truncate (n + 1) = (x * y).truncate (n + 1) := by
    simpa only [map_mul] using congrArg₂ (· * ·)
      (truncate_partialSum_eq p x n) (truncate_partialSum_eq p y n)
  have hc := congrArg (fun z : TruncatedWittVector p (n + 1) F =>
    z.coeff ⟨n, Nat.lt_succ_self n⟩) ht
  simp only [WittVector.coeff_truncate] at hc
  have hd : digits p (a * b) n = digits p (x * y) n := by simp only [digits, hc]
  rw [← hd]
  exact (term_le_value p ρ (a * b) n).trans
    (value_partialSum_product_le p O hO ρ hρ x y n)

end
end JoshiTeich.Act1Scene1.WittWeightedDigitMultiplication
