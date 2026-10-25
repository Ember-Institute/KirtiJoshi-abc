import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedDigitMultiplication

/-!
source-id: JT-SCENE1-WITT-WEIGHTED-DIGIT-NEGATION
source: Joshi II `se:ff-rings`, the integral Witt unit ball underlying
`pr:teichmuller-lift-A/B`.
fidelity: integral Witt images have digit norms at most one and weighted
value at most one. In particular -1 has value at most one; proved
submultiplicativity then gives invariance under negation. Original proofs.
boundary: Scene1/Derived; no multiplicative equality or completed B identity.
-/

namespace JoshiTeich.Act1Scene1.WittWeightedDigitNegation

open WittTeichmullerExpansion WittWeightedDigits
open scoped ENNReal
noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {F : Type*} [NormedField F] [CharP F p] [PerfectRing F p]

theorem norm_digits_map_le_one (O : Subring F) (hO : ∀ a : F, a ∈ O ↔ ‖a‖ ≤ 1)
    (a : WittVector p O) (n : ℕ) :
    ‖digits p (WittVector.map O.subtype a) n‖ ≤ 1 := by
  have hc : ‖(WittVector.map O.subtype a).coeff n‖ ≤ 1 := by
    rw [WittVector.map_coeff]
    exact (hO _).mp (a.coeff n).property
  rw [(expands_iff_coeff p _ _).mp (expands_digits p (WittVector.map O.subtype a)) n,
    norm_pow] at hc
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _)
    (pow_ne_zero n (Fact.out : p.Prime).ne_zero)).mp hc

theorem value_map_le_one (O : Subring F) (hO : ∀ a : F, a ∈ O ↔ ‖a‖ ≤ 1)
    (ρ : ℝ≥0∞) (hρ : ρ ≤ 1) (a : WittVector p O) :
    value p ρ (WittVector.map O.subtype a) ≤ 1 := by
  simpa only [ENNReal.ofReal_one] using
    value_le_of_bound p ρ hρ (WittVector.map O.subtype a) 1 (norm_digits_map_le_one p O hO a)

theorem value_neg_one_le_one (O : Subring F) (hO : ∀ a : F, a ∈ O ↔ ‖a‖ ≤ 1)
    (ρ : ℝ≥0∞) (hρ : ρ ≤ 1) : value p ρ (-1 : WittVector p F) ≤ 1 := by
  simpa only [map_neg, map_one] using value_map_le_one p O hO ρ hρ (-1 : WittVector p O)

theorem value_neg_le (O : Subring F) (hO : ∀ a : F, a ∈ O ↔ ‖a‖ ≤ 1)
    (ρ : ℝ≥0∞) (hρ : ρ ≤ 1) (x : WittVector p F) : value p ρ (-x) ≤ value p ρ x := by
  have h := WittWeightedDigitMultiplication.value_mul_le p O hO ρ hρ (-1) x
  rw [neg_one_mul] at h
  apply h.trans
  simpa only [one_mul] using mul_le_mul (value_neg_one_le_one p O hO ρ hρ)
    (le_rfl : value p ρ x ≤ value p ρ x) bot_le bot_le

theorem value_neg (O : Subring F) (hO : ∀ a : F, a ∈ O ↔ ‖a‖ ≤ 1)
    (ρ : ℝ≥0∞) (hρ : ρ ≤ 1) (x : WittVector p F) : value p ρ (-x) = value p ρ x := by
  apply le_antisymm (value_neg_le p O hO ρ hρ x)
  simpa only [neg_neg] using value_neg_le p O hO ρ hρ (-x)

end
end JoshiTeich.Act1Scene1.WittWeightedDigitNegation
