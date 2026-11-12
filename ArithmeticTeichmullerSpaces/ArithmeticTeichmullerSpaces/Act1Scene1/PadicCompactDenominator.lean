import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecificLimits.Basic

/-!
source-id: JT-SCENE1-PADIC-COMPACT-DENOMINATOR
source: compact continuous image boundedness and decay of powers of p.
fidelity: one p-power denominator clears all values of a continuous Q_p
function on a compact space, with a continuous lift to the original Z_p.
No pointwise choices of denominators or transported topology are used.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.PadicCompact
open Filter Topology
universe u
noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {X : Type u} [TopologicalSpace X] [CompactSpace X]

theorem exists_uniform_denominator (f : C(X, ℚ_[p])) :
    ∃ n : ℕ, ∀ x, ‖(p : ℚ_[p]) ^ n * f x‖ ≤ 1 := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn f.continuous.continuousOn
  have ht : Tendsto (fun n : ℕ => ‖(p : ℚ_[p])‖ ^ n * C) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (Padic.norm_p_lt_one (p := p))).mul_const C
  obtain ⟨n, hn⟩ := ((tendsto_order.mp ht).2 1 zero_lt_one).exists
  refine ⟨n, fun x => ?_⟩
  rw [norm_mul, norm_pow]
  exact (mul_le_mul_of_nonneg_left (hC x (Set.mem_univ x))
    (pow_nonneg (norm_nonneg _) n)).trans hn.le

def integralLift (f : C(X, ℚ_[p])) (n : ℕ)
    (hn : ∀ x, ‖(p : ℚ_[p]) ^ n * f x‖ ≤ 1) : C(X, ℤ_[p]) :=
  ⟨fun x => ⟨(p : ℚ_[p]) ^ n * f x, hn x⟩,
    (continuous_const.mul f.continuous).subtype_mk _⟩

theorem integralLift_coe (f : C(X, ℚ_[p])) (n : ℕ)
    (hn : ∀ x, ‖(p : ℚ_[p]) ^ n * f x‖ ≤ 1) (x : X) :
    (integralLift p f n hn x : ℚ_[p]) = (p : ℚ_[p]) ^ n * f x := rfl

end
end JoshiTeich.Act1Scene1.PadicCompact
