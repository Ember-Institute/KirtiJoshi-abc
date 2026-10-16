import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerSmallLogLift
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionDegree

/-!
source-id: JT-SCENE1-COMPLETION-SMALL-LOG-LIFT
source: actual completion valuation and ramification index, small-ball
logarithm surjectivity and original Kummer coefficients; Joshi III 3226--3236.
fidelity: at odd residue characteristic, the small-log condition for a
contracting nonzero parameter is exactly qOrder >= ramIdx. Powers satisfy
it eventually. No extra norm bound for the original parameter is assumed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion
open NumberField IsDedekindDomain WithZero
open JoshiTeich.Prologue.Arithmetic
open scoped Valued
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] (w : FinitePlace K)
local instance smallLogPrime : Fact (residueChar w).Prime := ⟨residueChar_prime w⟩
local instance smallLogCharZero : CharZero (completionAt K w) :=
  charZero_of_injective_ringHom (FinitePlace.embedding w.maximalIdeal).injective
local instance smallLogAlgebra : Algebra ℚ_[residueChar w] (completionAt K w) :=
  padicAlgebra (w := w) rfl
local instance smallLogContinuousSMul : ContinuousSMul ℚ_[residueChar w] (completionAt K w) :=
  continuousSMul_of_algebraMap _ _ (continuous_padicEmb (w := w) rfl)

private theorem smallLog_norm_prime_lt_one : ‖(residueChar w : completionAt K w)‖ < 1 := by
  have h := norm_natCast_prime_lt_one (p := residueChar w) (w := w) rfl
  rwa [← FinitePlace.embedding_apply, map_natCast] at h

theorem norm_le_prime_iff_qOrder_ge (y : completionAt K w) (hy0 : y ≠ 0) (hy1 : ‖y‖ < 1) :
    ‖y‖ ≤ ‖(residueChar w : completionAt K w)‖ ↔ ramIdx w ≤ completionQOrder w y := by
  rw [Valued.toNormedField.norm_le_iff, completionQOrder_valued w y hy0 hy1]
  have hp := valued_residueChar w
  rw [map_natCast] at hp
  rw [hp, exp_le_exp, neg_le_neg_iff, Int.ofNat_le]

theorem norm_le_smallLogRadius_iff_qOrder_ge (hp : Odd (residueChar w))
    (y : completionAt K w) (hy0 : y ≠ 0) (hy1 : ‖y‖ < 1) :
    ‖y‖ ≤ ‖2 * (residueChar w : completionAt K w)‖ ↔ ramIdx w ≤ completionQOrder w y := by
  rw [norm_mul, LocalPadicLog.norm_two_eq_one (residueChar_prime w) (smallLog_norm_prime_lt_one w) hp, one_mul]
  exact norm_le_prime_iff_qOrder_ge w y hy0 hy1

theorem paperNormalizedLog_mem_integralImage_of_qOrder (hp : Odd (residueChar w))
    (y : completionAt K w) (hy0 : y ≠ 0) (hy1 : ‖y‖ < 1)
    (hy : ramIdx w ≤ completionQOrder w y) :
    LocalPadicLog.paperNormalizedLog (residueChar w) y ∈
      LocalPadicLog.principalLogImage (residueChar w) (smallLog_norm_prime_lt_one w) :=
  LocalPadicLog.paperNormalizedLog_mem_principalLogImage_of_small _ _
    ((norm_le_smallLogRadius_iff_qOrder_ge w hp y hy0 hy1).mpr hy)

theorem eventually_paperNormalizedLog_mem_integralImage (y : completionAt K w) (hy : ‖y‖ < 1) :
    ∀ᶠ j : ℕ in Filter.atTop, LocalPadicLog.paperNormalizedLog (residueChar w) (y ^ j) ∈
      LocalPadicLog.principalLogImage (residueChar w) (smallLog_norm_prime_lt_one w) := by
  have hr : 0 < ‖2 * (residueChar w : completionAt K w)‖ := norm_pos_iff.mpr
    (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (residueChar_prime w).ne_zero))
  have ht := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hy).norm
  have he : ∀ᶠ j : ℕ in Filter.atTop, ‖y ^ j‖ < ‖2 * (residueChar w : completionAt K w)‖ :=
    (tendsto_order.mp ht).2 _ (by simpa only [norm_zero] using hr)
  exact he.mono fun j hj => LocalPadicLog.paperNormalizedLog_mem_principalLogImage_of_small _ _ hj.le

end
end JoshiTeich.Act1Scene1.LocalCompletion
