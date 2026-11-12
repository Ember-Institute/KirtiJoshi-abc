import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedDigitNegation

/-!
source-id: JT-SCENE1-WITT-WEIGHTED-TRUNCATION
source: Joshi II `se:ff-rings`, Gauss norms on bounded Teichmuller
expansions; the actual Witt init and truncate operations.
fidelity: truncating the genuine digits decreases the weighted value.
The resulting finite-head value respects truncated equality, is
ultrametric and invariant under negation. A strict dominant summand
cannot cancel, even with the actual Witt carries.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; product dominance must be proved separately.
-/

namespace JoshiTeich.Act1Scene1.WittWeightedTruncation

open WittTeichmullerExpansion WittWeightedDigits
open scoped ENNReal
noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {F : Type*} [NormedField F] [CharP F p] [PerfectRing F p]

def headValue (ρ : ℝ≥0∞) (N : ℕ) (x : WittVector p F) : ℝ≥0∞ :=
  value p ρ (WittVector.init N x)

theorem digits_init (N : ℕ) (x : WittVector p F) (n : ℕ) :
    digits p (WittVector.init N x) n = if n < N then digits p x n else 0 := by
  classical
  by_cases hn : n < N
  · simp only [digits, WittVector.init, WittVector.select, WittVector.coeff_mk, if_pos hn]
  · simp only [digits, WittVector.init, WittVector.select, WittVector.coeff_mk, if_neg hn, map_zero]

theorem headValue_le (ρ : ℝ≥0∞) (N : ℕ) (x : WittVector p F) :
    headValue p ρ N x ≤ value p ρ x := by
  apply iSup_le
  intro n
  rw [digits_init]
  split_ifs with hn
  · exact term_le_value p ρ x n
  · simp only [norm_zero, ENNReal.ofReal_zero, zero_mul]
    exact bot_le

theorem headValue_zero (ρ : ℝ≥0∞) (N : ℕ) : headValue p ρ N (0 : WittVector p F) = 0 := by
  apply le_antisymm
  · exact (headValue_le p ρ N 0).trans_eq (value_zero p ρ)
  · exact bot_le

theorem headValue_congr (ρ : ℝ≥0∞) (N : ℕ) {x y : WittVector p F}
    (h : x.truncate N = y.truncate N) : headValue p ρ N x = headValue p ρ N y := by
  change value p ρ (WittVector.init N x) = value p ρ (WittVector.init N y)
  congr 1
  apply WittVector.ext
  intro n
  simp only [WittVector.init, WittVector.select, WittVector.coeff_mk]
  split_ifs with hn
  · exact congrArg (fun z : TruncatedWittVector p N F => z.coeff ⟨n, hn⟩) h
  · rfl

variable (O : Subring F) (hO : ∀ a : F, a ∈ O ↔ ‖a‖ ≤ 1)
include O hO

theorem headValue_add_le_max (ρ : ℝ≥0∞) (hρ : ρ ≤ 1) (N : ℕ) (x y : WittVector p F) :
    headValue p ρ N (x + y) ≤ max (headValue p ρ N x) (headValue p ρ N y) := by
  change value p ρ (WittVector.init N (x + y)) ≤ _
  rw [WittVector.init_add]
  exact (headValue_le p ρ N _).trans
    (WittWeightedDigitAddition.value_add_le_max p O hO ρ hρ _ _)

theorem headValue_neg (ρ : ℝ≥0∞) (hρ : ρ ≤ 1) (N : ℕ) (x : WittVector p F) :
    headValue p ρ N (-x) = headValue p ρ N x := by
  have hle (z : WittVector p F) : headValue p ρ N (-z) ≤ headValue p ρ N z := by
    change value p ρ (WittVector.init N (-z)) ≤ _
    rw [WittVector.init_neg]
    exact (headValue_le p ρ N _).trans_eq
      (WittWeightedDigitNegation.value_neg p O hO ρ hρ _)
  exact le_antisymm (hle x) (by simpa only [neg_neg] using hle (-x))

theorem headValue_add_eq_left_of_lt (ρ : ℝ≥0∞) (hρ : ρ ≤ 1) (N : ℕ)
    (x y : WittVector p F) (h : headValue p ρ N y < headValue p ρ N x) :
    headValue p ρ N (x + y) = headValue p ρ N x := by
  apply le_antisymm
  · exact (headValue_add_le_max p O hO ρ hρ N x y).trans_eq (max_eq_left h.le)
  · have hb := headValue_add_le_max p O hO ρ hρ N (x + y) (-y)
    rw [add_neg_cancel_right, headValue_neg p O hO ρ hρ] at hb
    by_contra hn
    exact (not_lt_of_ge hb) (max_lt (lt_of_not_ge hn) h)

theorem headValue_sum_lt (ρ : ℝ≥0∞) (hρ : ρ ≤ 1) (N : ℕ)
    {ι : Type*} (s : Finset ι) (f : ι → WittVector p F) (C : ℝ≥0∞) (hC : 0 < C)
    (hf : ∀ i ∈ s, headValue p ρ N (f i) < C) :
    headValue p ρ N (∑ i ∈ s, f i) < C := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa only [Finset.sum_empty, headValue_zero] using hC
  | @insert i s hi ih =>
    intro hf
    rw [Finset.sum_insert hi]
    exact (headValue_add_le_max p O hO ρ hρ N _ _).trans_lt
      (max_lt (hf i (Finset.mem_insert_self i s))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))))

theorem headValue_sum_eq_dominant (ρ : ℝ≥0∞) (hρ : ρ ≤ 1) (N : ℕ)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → WittVector p F)
    (i : ι) (hi : i ∈ s) (hpos : 0 < headValue p ρ N (f i))
    (hf : ∀ j ∈ s, j ≠ i → headValue p ρ N (f j) < headValue p ρ N (f i)) :
    headValue p ρ N (∑ j ∈ s, f j) = headValue p ρ N (f i) := by
  rw [← Finset.add_sum_erase _ _ hi]
  apply headValue_add_eq_left_of_lt p O hO ρ hρ
  apply headValue_sum_lt p O hO ρ hρ N _ _ _ hpos
  intro j hj
  exact hf j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)

end
end JoshiTeich.Act1Scene1.WittWeightedTruncation
