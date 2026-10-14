import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorResidueNormDiscrete
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorResidueBounds

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-ATTAINED-RESIDUE-MAXIMUM
source: actual discrete residue spectral values and bounded tensor subsets.
fidelity: proves each nonzero coordinate on a bounded set attains its maximum
norm. No compactness or caller-supplied extremum certificate is used.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)

theorem exists_max_residueNorm (U : Set P.Tensor) (hU : Bornology.IsBounded U)
    (I : MaximalSpectrum P.Tensor)
    (hcoord : ∃ x ∈ U, Ideal.Quotient.mk I.asIdeal x ≠ 0) :
    ∃ x ∈ U, Ideal.Quotient.mk I.asIdeal x ≠ 0 ∧
      ∀ y ∈ U, P.residueNorm I (Ideal.Quotient.mk I.asIdeal y) ≤
        P.residueNorm I (Ideal.Quotient.mk I.asIdeal x) := by
  classical
  obtain ⟨B, hB⟩ := P.exists_uniform_residueNorm_bound hU
  let D := P.residueExponent I
  have hD : D ≠ 0 := Nat.factorial_ne_zero _
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  let Z : ℤ → Prop := fun k => ∃ x ∈ U, Ideal.Quotient.mk I.asIdeal x ≠ 0 ∧
    P.residueNorm I (Ideal.Quotient.mk I.asIdeal x) ^ D = (p : ℝ) ^ k
  have hZne : ∃ k, Z k := by
    obtain ⟨x, hx, hx0⟩ := hcoord
    obtain ⟨k, hk⟩ := P.exists_residueNorm_pow_eq_zpow I hx0
    exact ⟨k, x, hx, hx0, hk⟩
  have hZbdd : ∃ b : ℤ, ∀ k, Z k → k ≤ b := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((max B 0) ^ D) hp1
    refine ⟨n, ?_⟩
    rintro k ⟨x, hx, hx0, hk⟩
    have hlt : (p : ℝ) ^ k < (p : ℝ) ^ (n : ℤ) := by
      rw [← hk, zpow_natCast]
      exact (pow_le_pow_left₀ (P.residueNorm_nonneg I _)
        ((hB x hx I).trans (le_max_left B 0)) D).trans_lt hn
    exact ((zpow_lt_zpow_iff_right₀ hp1).mp hlt).le
  obtain ⟨b, ⟨x, hx, hx0, hkx⟩, hb⟩ := Int.exists_greatest_of_bdd hZbdd hZne
  refine ⟨x, hx, hx0, fun y hy => ?_⟩
  by_cases hy0 : Ideal.Quotient.mk I.asIdeal y = 0
  · rw [hy0, P.residueNorm_zero]
    exact P.residueNorm_nonneg I _
  · obtain ⟨k, hky⟩ := P.exists_residueNorm_pow_eq_zpow I hy0
    have hle := zpow_le_zpow_right₀ hp1.le (hb k ⟨y, hy, hy0, hky⟩)
    rw [← hky, ← hkx] at hle
    exact (pow_le_pow_iff_left₀ (P.residueNorm_nonneg I _)
      (P.residueNorm_nonneg I _) hD).mp hle

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
