import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedMonomial

/-!
source-id: JT-SCENE1-WITT-WEIGHTED-MULTIPLICATIVITY
source: Joshi II `se:ff-rings`, the multiplicative rho norms defining B.
fidelity: expands a product in the actual truncated Witt ring. The least
maximizing digit pair is its unique dominant summand at that truncation;
the proved ultrametric laws exclude cancellation by all other summands.
This proves multiplicativity for genuine uniformly bounded digits.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; localization and completion consumers and the
paper B/period/BK identities remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.WittWeightedMultiplicativity

open WittTeichmullerExpansion WittWeightedDigits WittWeightedTruncation
open WittWeightedMonomial WittWeightedDigitMaximum
open scoped ENNReal
noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {F : Type*} [NormedField F] [CharP F p] [PerfectRing F p]

theorem partialSum_product_eq_sum (x y : WittVector p F) (N : ℕ) :
    partialSum p (digits p x) N * partialSum p (digits p y) N =
      ∑ q ∈ (Finset.Iic N) ×ˢ (Finset.Iic N),
        monomial p (digits p x q.1 * digits p y q.2) (q.1 + q.2) := by
  simp only [Finset.sum_product, partialSum, Finset.sum_mul, Finset.mul_sum, monomial,
    WittWeightedDigitMultiplication.monomial_mul]
  rw [Finset.sum_comm]

theorem headValue_partialSum_product (ρ : ℝ≥0∞) (x y : WittVector p F) (N : ℕ) :
    headValue p ρ (N + 1) (partialSum p (digits p x) N * partialSum p (digits p y) N) =
      headValue p ρ (N + 1) (x * y) := by
  apply headValue_congr p ρ (N + 1)
  rw [map_mul, map_mul, WittWeightedDigitMultiplication.truncate_partialSum_eq,
    WittWeightedDigitMultiplication.truncate_partialSum_eq]

theorem value_mul (O : Subring F) (hO : ∀ a : F, a ∈ O ↔ ‖a‖ ≤ 1)
    (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ < 1) (x y : WittVector p F)
    (C D : ℝ) (hC : ∀ n, ‖digits p x n‖ ≤ C) (hD : ∀ n, ‖digits p y n‖ ≤ D) :
    value p ρ (x * y) = value p ρ x * value p ρ y := by
  by_cases hx : x = 0
  · simp only [hx, zero_mul, value_zero]
  by_cases hy : y = 0
  · simp only [hy, mul_zero, value_zero]
  obtain ⟨i, hi, hxi, hxlt⟩ := exists_first_max p ρ hρ1 x C hC
  obtain ⟨j, hj, hyj, hylt⟩ := exists_first_max p ρ hρ1 y D hD
  have hρtop : ρ ≠ ⊤ := (hρ1.trans ENNReal.one_lt_top).ne
  have hr : 0 < ρ.toReal := ENNReal.toReal_pos hρ0 hρtop
  have hxi0 : 0 < realTerm p ρ x i :=
    mul_pos (norm_pos_iff.mpr (maximizing_digit_ne_zero p ρ hρ0 x hx i hi)) (pow_pos hr i)
  have hyj0 : 0 < realTerm p ρ y j :=
    mul_pos (norm_pos_iff.mpr (maximizing_digit_ne_zero p ρ hρ0 y hy j hj)) (pow_pos hr j)
  let N := i + j
  let s := (Finset.Iic N) ×ˢ (Finset.Iic N)
  let f : ℕ × ℕ → WittVector p F := fun q =>
    monomial p (digits p x q.1 * digits p y q.2) (q.1 + q.2)
  have hmem : (i, j) ∈ s := Finset.mem_product.mpr
    ⟨Finset.mem_Iic.mpr (Nat.le_add_right i j), Finset.mem_Iic.mpr (Nat.le_add_left j i)⟩
  have hmain : headValue p ρ (N + 1) (f (i, j)) = value p ρ x * value p ρ y := by
    rw [headValue_monomial_of_lt p ρ _ (i + j) (N + 1) (Nat.lt_succ_self N)]
    exact product_monomial_value p ρ x y i j hi hj
  have hpos : 0 < headValue p ρ (N + 1) (f (i, j)) := by
    rw [hmain]
    apply pos_iff_ne_zero.mpr
    apply mul_ne_zero
    · exact fun h => hx ((value_eq_zero_iff p ρ hρ0 x).mp h)
    · exact fun h => hy ((value_eq_zero_iff p ρ hρ0 y).mp h)
  have hsum : headValue p ρ (N + 1) (∑ q ∈ s, f q) = headValue p ρ (N + 1) (f (i, j)) := by
    apply headValue_sum_eq_dominant p O hO ρ hρ1.le (N + 1) s f (i, j) hmem hpos
    rintro ⟨a, b⟩ _ hne
    by_cases hab : a + b ≤ N
    · apply (headValue_le p ρ (N + 1) _).trans_lt
      rw [headValue_monomial_of_lt p ρ _ (i + j) (N + 1) (Nat.lt_succ_self N)]
      apply (ENNReal.toReal_lt_toReal (value_monomial_ne_top p ρ hρtop _ _)
        (value_monomial_ne_top p ρ hρtop _ _)).mp
      rw [product_monomial_value_toReal, product_monomial_value_toReal]
      exact GeometricDominantTerm.product_pair_lt (realTerm p ρ x) (realTerm p ρ y) i j
        (realTerm_nonneg p ρ x) (realTerm_nonneg p ρ y) hxi0 hyj0 hxi hyj hxlt hylt a b hab hne
    · rw [headValue_monomial_of_le p ρ _ (a + b) (N + 1) (by omega)]
      exact hpos
  have hhead : headValue p ρ (N + 1) (x * y) = value p ρ x * value p ρ y := by
    rw [← headValue_partialSum_product p ρ x y N, partialSum_product_eq_sum]
    exact hsum.trans hmain
  apply le_antisymm (WittWeightedDigitMultiplication.value_mul_le p O hO ρ hρ1.le x y)
  rw [← hhead]
  exact headValue_le p ρ (N + 1) (x * y)

end
end JoshiTeich.Act1Scene1.WittWeightedMultiplicativity
