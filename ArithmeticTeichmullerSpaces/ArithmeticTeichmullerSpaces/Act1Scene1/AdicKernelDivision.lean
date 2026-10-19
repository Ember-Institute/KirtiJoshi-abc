import Mathlib.RingTheory.AdicCompletion.Basic

/-!
source-id: JT-SCENE1-ADIC-KERNEL-DIVISION
source: the p-adic division argument for the principal Fontaine kernel in
Joshi II pa:Mochizuki-Ansatz (838); Mathlib algebraic adic completeness.
fidelity: a proved successive-division law in an ideal yields actual
divisibility in the same complete ring. The quotient is constructed by
complete approx sums; no closedness of a principal ideal is assumed.
Original proofs; Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.AdicKernelDivision

open scoped BigOperators
noncomputable section
variable {R : Type*} [CommRing R]

/-- Successive divisions converge in the original ring, with an exact final product. -/
theorem exists_factor (p ξ : R) [IsAdicComplete (Ideal.span {p}) R]
    (K : Ideal R)
    (hstep : ∀ a : K, ∃ c : R, ∃ r : K, (a : R) = ξ * c + p * (r : R))
    (a : K) : ∃ b : R, (a : R) = ξ * b := by
  classical
  choose c r hr using hstep
  let residual : ℕ → K := fun n => r^[n] a
  let approx : ℕ → R := fun n => ∑ i ∈ Finset.range n, p ^ i * c (residual i)
  have hres (n : ℕ) : (a : R) = ξ * approx n + p ^ n * (residual n : R) := by
    induction n with
    | zero => simp [approx, residual]
    | succ n ih =>
      have hn : (residual n : R) = ξ * c (residual n) + p * (residual (n + 1) : R) := by
        simpa only [residual, Function.iterate_succ_apply'] using hr (residual n)
      rw [ih, hn]
      simp only [approx, Finset.sum_range_succ, pow_succ]
      ring
  let I : Ideal R := Ideal.span {p}
  have hp : p ∈ I := Ideal.subset_span (by simp)
  have hseq : AdicCompletion.IsAdicCauchy I R approx := by
    apply (AdicCompletion.isAdicCauchy_iff I R approx).mpr
    intro n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    have he : approx n - approx (n + 1) = -(p ^ n * c (residual n)) := by
      simp only [approx, Finset.sum_range_succ]
      ring
    rw [he]
    exact (I ^ n).neg_mem (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hp n))
  obtain ⟨b, hb⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I R) hseq
  refine ⟨b, ?_⟩
  apply sub_eq_zero.mp
  apply IsHausdorff.haus (inferInstance : IsHausdorff I R)
  intro n
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  have hq : approx n - b ∈ I ^ n := by
    simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using hb n
  have ha : (a : R) - ξ * approx n ∈ I ^ n := by
    rw [hres n, add_sub_cancel_left]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hp n)
  have he : (a : R) - ξ * b = ((a : R) - ξ * approx n) + ξ * (approx n - b) := by ring
  rw [he]
  exact Ideal.add_mem _ ha (Ideal.mul_mem_left _ _ hq)

theorem eq_span (p ξ : R) [IsAdicComplete (Ideal.span {p}) R]
    (K : Ideal R) (hξ : ξ ∈ K)
    (hstep : ∀ a : K, ∃ c : R, ∃ r : K, (a : R) = ξ * c + p * (r : R)) :
    K = Ideal.span {ξ} := by
  apply le_antisymm
  · intro a ha
    obtain ⟨b, hb⟩ := exists_factor p ξ K hstep ⟨a, ha⟩
    exact Ideal.mem_span_singleton.mpr ⟨b, hb⟩
  · exact Ideal.span_le.mpr (by simpa using hξ)

end
end JoshiTeich.Act1Scene1.AdicKernelDivision
