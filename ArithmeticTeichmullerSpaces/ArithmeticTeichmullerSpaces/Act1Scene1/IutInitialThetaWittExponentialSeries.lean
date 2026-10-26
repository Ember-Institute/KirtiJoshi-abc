import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittExponentialCoefficients
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittMultiplicativeNorm
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoUltrametric
import ArithmeticTeichmullerSpaces.Act1Scene1.UltrametricLogTailBounds
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-EXPONENTIAL-SERIES
source: Joshi II `pr:teichmuller-lift-A`, the multiplicative-formal-group
period construction and its exponential inverse.
fidelity: the actual 1/n! scalar images define an absolutely convergent
exponential series in the original rho completion whenever norm(x)<rho.
The geometric term bound also bounds norm(exp(x)-1) by norm(x)/rho<1.
No completion, topology or exponential law is supplied as input.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; exp/log inverse identities and full period
representation remain separate obligations. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittExponentialSeries

open JoshiTeich.Prologue InitialThetaWittAllRadiusPadicScalars
open InitialThetaWittExponentialCoefficients
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Ring (ρ : Radius) := InitialThetaWittRhoCompletion.Completed D w ρ

theorem radius_toReal_pos (ρ : Radius) : 0 < ρ.val.toReal :=
  ENNReal.toReal_pos ρ.property.1.ne' (ρ.property.2.trans ENNReal.one_lt_top).ne

def term (ρ : Radius) (x : Ring D w ρ) (n : ℕ) : Ring D w ρ :=
  completedPadicMap D w ρ (coefficient D w n) * x ^ n

theorem term_zero (ρ : Radius) (x : Ring D w ρ) : term D w ρ x 0 = 1 := by
  simp only [term, coefficient_zero, map_one, pow_zero, mul_one]

theorem norm_term_le (ρ : Radius) (x : Ring D w ρ) (n : ℕ) :
    ‖term D w ρ x n‖ ≤ (‖x‖ / ρ.val.toReal) ^ n := by
  rw [term, norm_mul, norm_pow]
  calc
    _ ≤ (ρ.val.toReal)⁻¹ ^ n * ‖x‖ ^ n :=
      mul_le_mul_of_nonneg_right (norm_coefficient_le D w ρ n) (pow_nonneg (norm_nonneg x) n)
    _ = _ := by rw [div_pow, inv_pow, div_eq_inv_mul]

theorem summable_norm_term (ρ : Radius) (x : Ring D w ρ) (hx : ‖x‖ < ρ.val.toReal) :
    Summable (fun n : ℕ => ‖term D w ρ x n‖) :=
  Summable.of_nonneg_of_le (fun n => norm_nonneg _) (norm_term_le D w ρ x)
    (summable_geometric_of_lt_one (div_nonneg (norm_nonneg _) (radius_toReal_pos ρ).le)
      ((div_lt_one (radius_toReal_pos ρ)).mpr hx))

def exp (ρ : Radius) (x : Ring D w ρ) : Ring D w ρ := ∑' n : ℕ, term D w ρ x n

theorem hasSum_exp (ρ : Radius) (x : Ring D w ρ) (hx : ‖x‖ < ρ.val.toReal) :
    HasSum (term D w ρ x) (exp D w ρ x) := (summable_norm_term D w ρ x hx).of_norm.hasSum

theorem exp_zero (ρ : Radius) : exp D w ρ 0 = 1 := by
  unfold exp
  rw [tsum_eq_single 0]
  · exact term_zero D w ρ 0
  · intro n hn
    simp only [term, zero_pow hn, mul_zero]

theorem hasSum_exp_tail (ρ : Radius) (x : Ring D w ρ) (hx : ‖x‖ < ρ.val.toReal) :
    HasSum (fun n : ℕ => term D w ρ x (n + 1)) (exp D w ρ x - 1) := by
  simpa only [Finset.sum_range_one, term_zero] using
    (hasSum_nat_add_iff' 1).mpr (hasSum_exp D w ρ x hx)

theorem norm_exp_sub_one_le (ρ : Radius) (x : Ring D w ρ) (hx : ‖x‖ < ρ.val.toReal) :
    ‖exp D w ρ x - 1‖ ≤ ‖x‖ / ρ.val.toReal := by
  have hs := hasSum_exp_tail D w ρ x hx
  rw [← hs.tsum_eq]
  apply UltrametricLogTailBounds.norm_tsum_le_of_forall_le _ hs.summable _
    (div_nonneg (norm_nonneg _) (radius_toReal_pos ρ).le)
  intro n
  apply (norm_term_le D w ρ x (n + 1)).trans
  have h := pow_le_pow_of_le_one
    (div_nonneg (norm_nonneg x) (radius_toReal_pos ρ).le)
    ((div_lt_one (radius_toReal_pos ρ)).mpr hx).le (Nat.le_add_left 1 n)
  simpa only [pow_one] using h

theorem norm_exp_sub_one_lt_one (ρ : Radius) (x : Ring D w ρ) (hx : ‖x‖ < ρ.val.toReal) :
    ‖exp D w ρ x - 1‖ < 1 :=
  (norm_exp_sub_one_le D w ρ x hx).trans_lt ((div_lt_one (radius_toReal_pos ρ)).mpr hx)

end
end JoshiTeich.Act1Scene1.InitialThetaWittExponentialSeries
