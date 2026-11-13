import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.RingTheory.Radical.NatInt

set_option autoImplicit false

open UniqueFactorizationMonoid

theorem abc.goal.lt_constant_mul_fix (ε : ℝ) (hε : 0 < ε) : ∃ K : ℝ,
    ∀ (a b c : ℕ), 0 < a → 0 < b → 0 < c →
      ({a, b, c} : Set ℕ).Pairwise Nat.Coprime → a + b = c →
      (c : ℝ) < K * ((radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε) := by sorry
