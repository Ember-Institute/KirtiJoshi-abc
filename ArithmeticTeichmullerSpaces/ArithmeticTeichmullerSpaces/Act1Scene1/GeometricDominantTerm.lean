import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Max

/-!
source-id: JT-SCENE1-GEOMETRIC-DOMINANT-TERM
source: Joshi II `se:ff-rings`, the Gauss maximum in bounded
rho-weighted Teichmuller expansions before `pr:teichmuller-lift-A/B`.
fidelity: a nonnegative real sequence tending to zero attains a maximum
at a least index. Before that index all inequalities are strict. For
two such positive maxima, their product is strictly larger than every
other pair whose total index is no greater than the two least indices.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; Witt carries and multiplicative equality
are separate obligations.
-/

namespace JoshiTeich.Act1Scene1.GeometricDominantTerm

open scoped Topology

theorem exists_max_of_tendsto_zero (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (ht : Filter.Tendsto f Filter.atTop (𝓝 0)) : ∃ i, ∀ n, f n ≤ f i := by
  classical
  by_cases hz : ∀ n, f n = 0
  · exact ⟨0, fun n => by rw [hz n, hz 0]⟩
  · obtain ⟨k, hk⟩ := not_forall.mp hz
    have hkpos : 0 < f k := lt_of_le_of_ne (hf k) (Ne.symm hk)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hkpos))
    let s := Finset.range (N + k + 1)
    have hkmem : k ∈ s := Finset.mem_range.mpr (by omega)
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image s f ⟨k, hkmem⟩
    refine ⟨i, fun n => ?_⟩
    by_cases hn : n ∈ s
    · exact hmax n hn
    · have hnN : N ≤ n := by
        have hn' : ¬ n < N + k + 1 := fun h => hn (Finset.mem_range.mpr h)
        omega
      exact (hN n hnN).le.trans (hmax k hkmem)

theorem exists_first_max_of_tendsto_zero (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (ht : Filter.Tendsto f Filter.atTop (𝓝 0)) :
    ∃ i, (∀ n, f n ≤ f i) ∧ ∀ n < i, f n < f i := by
  classical
  have hex := exists_max_of_tendsto_zero f hf ht
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro n hn
  apply lt_of_le_of_ne (Nat.find_spec hex n)
  intro he
  have hm : ∀ j, f j ≤ f n := by
    rw [he]
    exact Nat.find_spec hex
  exact (Nat.not_le_of_lt hn) (Nat.find_min' hex hm)

theorem product_pair_lt (f g : ℕ → ℝ) (i j : ℕ)
    (hf0 : ∀ n, 0 ≤ f n) (hg0 : ∀ n, 0 ≤ g n)
    (hfi : 0 < f i) (hgj : 0 < g j)
    (hf : ∀ n, f n ≤ f i) (hg : ∀ n, g n ≤ g j)
    (hfl : ∀ n < i, f n < f i) (hgl : ∀ n < j, g n < g j)
    (a b : ℕ) (hab : a + b ≤ i + j) (hne : (a, b) ≠ (i, j)) :
    f a * g b < f i * g j := by
  by_cases hai : a < i
  · exact (mul_le_mul_of_nonneg_left (hg b) (hf0 a)).trans_lt
      (mul_lt_mul_of_pos_right (hfl a hai) hgj)
  · have hbj : b < j := by
      by_contra hb
      have haeq : a = i := by omega
      have hbeq : b = j := by omega
      exact hne (Prod.ext haeq hbeq)
    exact (mul_le_mul_of_nonneg_right (hf a) (hg0 b)).trans_lt
      (mul_lt_mul_of_pos_left (hgl b hbj) hfi)

end JoshiTeich.Act1Scene1.GeometricDominantTerm
