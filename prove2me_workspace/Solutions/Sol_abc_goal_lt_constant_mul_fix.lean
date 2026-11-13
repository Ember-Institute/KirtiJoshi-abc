import Theorems.Thm_AbcAdaptation_classical

set_option autoImplicit false

open UniqueFactorizationMonoid

theorem solution (ε : ℝ) (hε : 0 < ε) : ∃ K : ℝ,
    ∀ (a b c : ℕ), 0 < a → 0 < b → 0 < c →
      ({a, b, c} : Set ℕ).Pairwise Nat.Coprime → a + b = c →
      (c : ℝ) < K * ((radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε) :=
  AbcAdaptation.platformABC_of_classicalABC AbcAdaptation.classical ε hε

#print axioms solution
