/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/Takeuchi.lean
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Solutions.Source_ReferenceIutCanLiftFricke
import Solutions.Source_ReferenceIutCanLiftTakeuchiMarkov

set_option autoImplicit false

open Subgroup
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi

open Fricke (tr tr_mul_comm tr_inv tr_inv_mul tr_commutator_eq_neg_two_iff)

/-- The trace triple `(x, y, z)` is *realised* in `Γ` if `Γ = ⟨A, B⟩` with `tr A = x`,
`tr B = y`, `tr AB = z`. -/
def Realizes (Γ : Subgroup SL(2, ℝ)) (x y z : ℝ) : Prop :=
  ∃ A B : SL(2, ℝ), Subgroup.closure {A, B} = Γ ∧ tr A = x ∧ tr B = y ∧ tr (A * B) = z

namespace Realizes

variable {Γ : Subgroup SL(2, ℝ)} {x y z : ℝ}

lemma mem {A B : SL(2, ℝ)} (h : Subgroup.closure {A, B} = Γ) : A ∈ Γ ∧ B ∈ Γ := by
  subst h
  exact ⟨subset_closure (by simp), subset_closure (by simp)⟩

/-- The Nielsen move `(A, B) ↦ (B, A)`. -/
lemma swap (h : Realizes Γ x y z) : Realizes Γ y x z := by
  obtain ⟨A, B, hcl, hx, hy, hz⟩ := h
  exact ⟨B, A, by rw [Set.pair_comm]; exact hcl, hy, hx, by rw [tr_mul_comm]; exact hz⟩

/-- The Nielsen move `(A, B) ↦ (B, (AB)⁻¹)`. -/
lemma cycle (h : Realizes Γ x y z) : Realizes Γ y z x := by
  obtain ⟨A, B, hcl, hx, hy, hz⟩ := h
  refine ⟨B, (A * B)⁻¹, ?_, hy, by rw [tr_inv, hz], ?_⟩
  · rw [← hcl]
    have hA : A ∈ Subgroup.closure {A, B} := subset_closure (by simp)
    have hB : B ∈ Subgroup.closure {A, B} := subset_closure (by simp)
    have hB' : B ∈ Subgroup.closure {B, (A * B)⁻¹} := subset_closure (by simp)
    have hAB' : (A * B)⁻¹ ∈ Subgroup.closure {B, (A * B)⁻¹} := subset_closure (by simp)
    apply le_antisymm
    · rw [closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨hB, inv_mem (mul_mem hA hB)⟩
    · rw [closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨?_, hB'⟩
      simpa [mul_assoc] using mul_mem (inv_mem hAB') (inv_mem hB')
  · rw [_root_.mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul, tr_inv, hx]

/-- The Nielsen move `(A, B) ↦ (A⁻¹, B)`: the Vieta flip `z ↦ xy - z`. -/
lemma flip (h : Realizes Γ x y z) : Realizes Γ x y (x * y - z) := by
  obtain ⟨A, B, hcl, hx, hy, hz⟩ := h
  refine ⟨A⁻¹, B, ?_, by rw [tr_inv, hx], hy, by rw [tr_inv_mul, hx, hy, hz]⟩
  rw [← hcl]
  have hA : A ∈ Subgroup.closure {A, B} := subset_closure (by simp)
  have hB : B ∈ Subgroup.closure {A, B} := subset_closure (by simp)
  have hA' : A⁻¹ ∈ Subgroup.closure {A⁻¹, B} := subset_closure (by simp)
  have hB' : B ∈ Subgroup.closure {A⁻¹, B} := subset_closure (by simp)
  apply le_antisymm
  · rw [closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨inv_mem hA, hB⟩
  · rw [closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨by simpa using inv_mem hA', hB'⟩

/-- Squared traces of a realised triple are integers if all squared traces in `Γ` are. -/
lemma sq_int (hint : ∀ γ ∈ Γ, ∃ m : ℤ, tr γ ^ 2 = m) (h : Realizes Γ x y z) :
    (∃ X : ℤ, x ^ 2 = X) ∧ (∃ Y : ℤ, y ^ 2 = Y) ∧ (∃ Z : ℤ, z ^ 2 = Z) := by
  obtain ⟨A, B, hcl, rfl, rfl, rfl⟩ := h
  obtain ⟨hA, hB⟩ := mem hcl
  exact ⟨hint A hA, hint B hB, hint _ (mul_mem hA hB)⟩

end Realizes

/-- **Nielsen descent.** In a group all of whose squared traces are integral, every realised
triple on the Fricke surface `x² + y² + z² = xyz` (other than `0`) can be moved by Nielsen moves
to one of Takeuchi's four triples. -/
theorem exists_takeuchiSq {Γ : Subgroup SL(2, ℝ)} (hint : ∀ γ ∈ Γ, ∃ m : ℤ, tr γ ^ 2 = m)
    (N : ℕ) : ∀ x y z : ℝ, Realizes Γ x y z → x ^ 2 + y ^ 2 + z ^ 2 = x * y * z →
      x ^ 2 + y ^ 2 + z ^ 2 ≤ N → 0 < x ^ 2 + y ^ 2 + z ^ 2 →
      ∃ x' y' z', Realizes Γ x' y' z' ∧ x' ^ 2 + y' ^ 2 + z' ^ 2 = x' * y' * z' ∧
        TakeuchiSq x' y' z' := by
  induction N with
  | zero =>
    intro x y z _ _ hN hpos
    push_cast at hN
    linarith
  | succ N ih =>
    intro x y z hr hrel hN hpos
    obtain ⟨⟨X, hX⟩, ⟨Y, hY⟩, ⟨Z, hZ⟩⟩ := hr.sq_int hint
    -- all coordinates are nonzero
    have hx : 0 < x ^ 2 := by
      rcases (sq_nonneg x).lt_or_eq with h | h
      · exact h
      · have hx0 : x = 0 := by nlinarith
        subst hx0
        nlinarith [sq_nonneg y, sq_nonneg z]
    have hy : 0 < y ^ 2 := by
      rcases (sq_nonneg y).lt_or_eq with h | h
      · exact h
      · have hy0 : y = 0 := by nlinarith
        subst hy0
        nlinarith [sq_nonneg x, sq_nonneg z]
    have hz : 0 < z ^ 2 := by
      rcases (sq_nonneg z).lt_or_eq with h | h
      · exact h
      · have hz0 : z = 0 := by nlinarith
        subst hz0
        nlinarith [sq_nonneg x, sq_nonneg y]
    -- a Vieta flip that decreases the sum of squares
    have descend : ∀ a b c : ℝ, Realizes Γ a b c →
        a ^ 2 + b ^ 2 + c ^ 2 = a * b * c → a ^ 2 + b ^ 2 + c ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 →
        a ^ 2 * b ^ 2 < 2 * (a * b * c) →
        ∃ x' y' z', Realizes Γ x' y' z' ∧ x' ^ 2 + y' ^ 2 + z' ^ 2 = x' * y' * z' ∧
        TakeuchiSq x' y' z' := by
      intro a b c habc hrel' hsum hlt
      have hr' := habc.flip
      obtain ⟨⟨X', hX'⟩, ⟨Y', hY'⟩, ⟨Z', hZ'⟩⟩ := hr'.sq_int hint
      obtain ⟨⟨X'', hX''⟩, ⟨Y'', hY''⟩, ⟨Z'', hZ''⟩⟩ := habc.sq_int hint
      have hnew : (a * b - c) ^ 2 = a ^ 2 * b ^ 2 - 2 * (a * b * c) + c ^ 2 := by ring
      have hrel'' : a ^ 2 + b ^ 2 + (a * b - c) ^ 2 = a * b * (a * b - c) := by
        linear_combination hrel'
      have hlt' : a ^ 2 + b ^ 2 + (a * b - c) ^ 2 < a ^ 2 + b ^ 2 + c ^ 2 := by
        rw [hnew]; linarith
      -- integrality of the two sums
      have hint1 : ((X' + Y' + Z' : ℤ) : ℝ) < ((X'' + Y'' + Z'' : ℤ) : ℝ) := by
        push_cast; rw [← hX', ← hY', ← hZ', ← hX'', ← hY'', ← hZ'']; exact hlt'
      have hint1' : X' + Y' + Z' + 1 ≤ X'' + Y'' + Z'' := by exact_mod_cast hint1
      have hle : a ^ 2 + b ^ 2 + (a * b - c) ^ 2 ≤ N := by
        have h1 : ((X' + Y' + Z' + 1 : ℤ) : ℝ) ≤ ((X'' + Y'' + Z'' : ℤ) : ℝ) := by
          exact_mod_cast hint1'
        push_cast at h1
        rw [← hX', ← hY', ← hZ', ← hX'', ← hY'', ← hZ'', hsum] at h1
        push_cast at hN
        linarith
      have hpos' : 0 < a ^ 2 + b ^ 2 + (a * b - c) ^ 2 := by
        have : 0 < a ^ 2 := by
          rcases (sq_nonneg a).lt_or_eq with h | h
          · exact h
          · have ha0 : a = 0 := by nlinarith
            subst ha0
            nlinarith [sq_nonneg b, sq_nonneg c]
        positivity
      exact ih _ _ _ hr' hrel'' hle hpos'
    by_cases h1 : x ^ 2 * y ^ 2 < 2 * (x * y * z)
    · exact descend x y z hr hrel rfl h1
    by_cases h2 : y ^ 2 * z ^ 2 < 2 * (y * z * x)
    · exact descend y z x hr.cycle (by linear_combination hrel) (by ring) h2
    by_cases h3 : z ^ 2 * x ^ 2 < 2 * (z * x * y)
    · exact descend z x y hr.cycle.cycle (by linear_combination hrel) (by ring) h3
    -- reduced triple: sort and classify
    push Not at h1 h2 h3
    rcases le_total (x ^ 2) (y ^ 2) with hxy | hxy <;>
    rcases le_total (y ^ 2) (z ^ 2) with hyz | hyz <;>
    rcases le_total (x ^ 2) (z ^ 2) with hxz | hxz
    · exact ⟨x, y, z, hr, hrel, takeuchiSq_of_sorted hX hY hZ hrel hx hxy hyz h1⟩
    · exact ⟨x, y, z, hr, hrel, takeuchiSq_of_sorted hX hY hZ hrel hx hxy hyz h1⟩
    · exact ⟨x, z, y, hr.swap.cycle, by linear_combination hrel,
        takeuchiSq_of_sorted hX hZ hY (by linear_combination hrel)
        hx hxz hyz (by linarith)⟩
    · exact ⟨z, x, y, hr.cycle.cycle, by linear_combination hrel,
        takeuchiSq_of_sorted hZ hX hY
        (by linear_combination hrel) hz hxz hxy (by linarith)⟩
    · exact ⟨y, x, z, hr.swap, by linear_combination hrel,
        takeuchiSq_of_sorted hY hX hZ (by linear_combination hrel)
        hy hxy hxz (by linarith)⟩
    · exact ⟨y, z, x, hr.cycle, by linear_combination hrel,
        takeuchiSq_of_sorted hY hZ hX (by linear_combination hrel)
        hy hyz hxz (by linarith)⟩
    · exact ⟨z, y, x, hr.swap.cycle.cycle, by linear_combination hrel,
        takeuchiSq_of_sorted hZ hY hX
        (by linear_combination hrel) hz hyz hxy (by linarith)⟩
    · exact ⟨z, y, x, hr.swap.cycle.cycle, by linear_combination hrel,
        takeuchiSq_of_sorted hZ hY hX
        (by linear_combination hrel) hz hyz hxy (by linarith)⟩

/-- **Takeuchi's diophantine reduction.** A `(1;∞)`-group `⟨A, B⟩` with `tr A ≠ 0` all of whose
squared traces are integers has a Nielsen-equivalent generating pair (again with
`tr [A', B'] = -2`) whose squared trace triple is `(9,9,9)`, `(8,8,16)`, `(5,20,25)` or
`(6,12,18)`. -/
theorem takeuchi_one_infty_of_int {A B : SL(2, ℝ)} (hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2)
    (hA : tr A ≠ 0) (hint : ∀ γ ∈ Subgroup.closure {A, B}, ∃ m : ℤ, tr γ ^ 2 = m) :
    ∃ A' B' : SL(2, ℝ), Subgroup.closure {A', B'} = Subgroup.closure {A, B} ∧
      tr (A' * B' * A'⁻¹ * B'⁻¹) = -2 ∧ TakeuchiSq (tr A') (tr B') (tr (A' * B')) := by
  have hrel := (tr_commutator_eq_neg_two_iff A B).mp hcomm
  have hr : Realizes (Subgroup.closure {A, B}) (tr A) (tr B) (tr (A * B)) :=
    ⟨A, B, rfl, rfl, rfl, rfl⟩
  obtain ⟨N, hN⟩ := exists_nat_ge (tr A ^ 2 + tr B ^ 2 + tr (A * B) ^ 2)
  have hpos : 0 < tr A ^ 2 + tr B ^ 2 + tr (A * B) ^ 2 := by positivity
  obtain ⟨x, y, z, ⟨A', B', hcl, rfl, rfl, rfl⟩, hrel', hT⟩ :=
    exists_takeuchiSq hint N _ _ _ hr hrel hN hpos
  exact ⟨A', B', hcl, (tr_commutator_eq_neg_two_iff A' B').mpr hrel', hT⟩

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi
