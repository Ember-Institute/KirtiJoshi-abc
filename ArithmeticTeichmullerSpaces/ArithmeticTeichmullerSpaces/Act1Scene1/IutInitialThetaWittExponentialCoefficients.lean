import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittLogDenominatorBounds
import Mathlib.Tactic.FieldSimp

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-EXPONENTIAL-COEFFICIENTS
source: Joshi II `pr:teichmuller-lift-A`, the multiplicative-formal-group
description of the period space and the ordinary exponential inverse.
fidelity: uses the actual coefficients 1/n! in Q_p, proves their binomial
product identity, and bounds their image at every original radius by
rho^(-n), using the proved factorial p-valuation bound.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; convergence and inverse-period construction
are separate consumers. No exponential law is input. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittExponentialCoefficients

open JoshiTeich.Prologue InitialThetaWittAllRadiusPadicScalars
open InitialThetaWittLogDenominatorBounds
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def coefficient (n : ℕ) : Padic (Arithmetic.residueChar w.1) := (n.factorial : Padic (Arithmetic.residueChar w.1))⁻¹

theorem coefficient_zero : coefficient D w 0 = 1 := by simp [coefficient]
theorem coefficient_one : coefficient D w 1 = 1 := by simp [coefficient]

theorem coefficient_mul (n k : ℕ) (hk : k ≤ n) :
    coefficient D w k * coefficient D w (n - k) =
      (n.choose k : Padic (Arithmetic.residueChar w.1)) * coefficient D w n := by
  have h : (n.choose k : Padic (Arithmetic.residueChar w.1)) *
      (k.factorial : Padic (Arithmetic.residueChar w.1)) * (n - k).factorial = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have h0 : (k.factorial : Padic (Arithmetic.residueChar w.1)) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have h1 : ((n - k).factorial : Padic (Arithmetic.residueChar w.1)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero
  have hn : (n.factorial : Padic (Arithmetic.residueChar w.1)) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  unfold coefficient
  field_simp
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h.symm

theorem norm_coefficient_le (ρ : Radius) (n : ℕ) :
    ‖completedPadicMap D w ρ (coefficient D w n)‖ ≤ (ρ.val.toReal)⁻¹ ^ n := by
  rw [coefficient, norm_inverse_natCast D w ρ n.factorial n.factorial_ne_zero, one_div, inv_pow]
  have hpos : 0 < ρ.val.toReal :=
    ENNReal.toReal_pos ρ.property.1.ne' (ρ.property.2.trans ENNReal.one_lt_top).ne
  have hle : ρ.val.toReal ≤ 1 := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_le_toReal (ρ.property.2.trans ENNReal.one_lt_top).ne ENNReal.one_ne_top).mpr ρ.property.2.le
  exact (inv_le_inv₀ (pow_pos hpos _) (pow_pos hpos _)).mpr
    (pow_le_pow_of_le_one hpos.le hle (padicValNat_factorial_le (Arithmetic.residueChar w.1) n))

end
end JoshiTeich.Act1Scene1.InitialThetaWittExponentialCoefficients
