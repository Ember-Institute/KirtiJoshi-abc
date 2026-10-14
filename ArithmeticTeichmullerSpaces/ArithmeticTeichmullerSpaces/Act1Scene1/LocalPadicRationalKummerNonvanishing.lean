import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerRationalDenominator
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalPadicKummerNonvanishing

/-!
source-id: JT-SCENE1-LOCAL-PADIC-RATIONAL-KUMMER-NONVANISHING
source: rational nonvanishing of local principal-unit Kummer classes.
fidelity: a rational coboundary would kill the integral class of a p-power
of the unit. The nonzero logarithm of that power contradicts integral
nonvanishing. No H1 injectivity, H^1_e membership or BK identity is assumed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalPadicLog
open scoped Valued
universe u v
noncomputable section
variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
variable [CharZero k] [CompleteSpace k]
variable {Ω : Type v} [Field Ω] [Algebra k Ω] [IsGalois k Ω] [Algebra.IsIntegral k Ω]
variable [CharZero Ω] [IsAlgClosed Ω] {p : ℕ} [Fact p.Prime]

theorem rationalKummer_ne_zero_of_log_ne_zero {a : k}
    (R : LocalKummer.RootTower (Ω := Ω) p a) (hpk : ‖(p : k)‖ < 1)
    (ha : ‖a - 1‖ < 1) (hlog : padicLog a ≠ 0) :
    LocalKummer.Rational.classOfCocycle p
      (R.continuousCocycleValue (Fact.out : p.Prime).pos (ne_zero_of_norm_sub_one_lt ha)) ≠ 0 := by
  intro h
  obtain ⟨n, hpow, hn⟩ := LocalKummer.Rational.integral_powClass_eq_zero_of_rational_eq_zero p R
    (ne_zero_of_norm_sub_one_lt ha) h
  have hsmall := norm_pow_sub_one_lt ha (p ^ n)
  have hlogpow : padicLog (a ^ (p ^ n)) ≠ 0 := by
    rw [padicLog_pow (Fact.out : p.Prime) hpk ha]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (pow_ne_zero n (Fact.out : p.Prime).ne_zero)) hlog
  exact integralKummer_ne_zero_of_log_ne_zero (R.pow (p ^ n)) hpk hsmall hlogpow hn

end
end JoshiTeich.Act1Scene1.LocalPadicLog
