import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerIntegralLogTopology

/-!
source-id: JT-SCENE1-SMALL-LOG-INTEGRAL-LIFT
source: actual small-ball logarithm surjectivity, original integral Kummer
classes and ordinary saturated log; Joshi III 3199--3236.
fidelity: every small log value has an explicitly constructed integral
Kummer lift of its original saturated exponential class. A normalized
paper principal class has such a lift when its parameter is in that ball.
boundary: Scene1/Derived; no H1e/BK comparison is assumed.
-/

namespace JoshiTeich.Act1Scene1.LocalPadicLog
open scoped Valued
universe u v
noncomputable section
variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
variable [CharZero k] [CompleteSpace k] (p : ℕ) [Fact p.Prime]
variable (hpk : ‖(p : k)‖ < 1)

def smallLogUnit (z : k) (hz : ‖z‖ ≤ ‖2 * (p : k)‖) : principalUnits (k := k) := by
  let a := Classical.choose (exists_padicLog_eq (Fact.out : p.Prime) hpk hz)
  have ha := (Classical.choose_spec (exists_padicLog_eq (Fact.out : p.Prime) hpk hz)).1
  have hsmall : ‖(1 + a : k) - 1‖ < 1 := by
    simpa only [add_sub_cancel_left] using ha.trans_lt (norm_two_mul_lt_one hpk)
  exact ⟨Units.mk0 (1 + a) (ne_zero_of_norm_sub_one_lt hsmall), hsmall⟩

theorem smallLogUnit_log (z : k) (hz : ‖z‖ ≤ ‖2 * (p : k)‖) :
    padicLog ((smallLogUnit p hpk z hz).1 : k) = z :=
  (Classical.choose_spec (exists_padicLog_eq (Fact.out : p.Prime) hpk hz)).2

variable {Ω : Type v} [Field Ω] [Algebra k Ω] [IsGalois k Ω] [Algebra.IsIntegral k Ω]
variable [CharZero Ω] [IsAlgClosed Ω]
variable [Algebra ℚ_[p] k] [ContinuousSMul ℚ_[p] k]
local notation "HI" => continuousCohomology 1 (LocalKummer.padicTateTopRep (K := k) (Ω := Ω) p)
local notation "HQ" => continuousCohomology 1 (LocalKummer.Rational.topRep (K := k) (Ω := Ω) p)

/-- The lift is a Kummer class of a small principal unit in the original base field. -/
def smallLogIntegralLift (z : k) (hz : ‖z‖ ≤ ‖2 * (p : k)‖) : HI :=
  LocalKummer.Rational.integralUnitClass p (smallLogUnit p hpk z hz).1

theorem smallLogIntegralLift_standardMap (z : k) (hz : ‖z‖ ≤ ‖2 * (p : k)‖) :
    LocalKummer.Rational.standardMap p (smallLogIntegralLift (Ω := Ω) p hpk z hz) =
      (saturatedExp (Ω := Ω) p hpk z : HQ) := by
  have he : principalSaturatedClass (Ω := Ω) p hpk (Additive.ofMul (smallLogUnit p hpk z hz)) =
      ⟨(saturatedExp (Ω := Ω) p hpk z : HQ), (saturatedExp (Ω := Ω) p hpk z).2⟩ := by
    apply (saturatedPadicLogEquiv p hpk).injective
    exact (saturatedPadicLog_principalSaturatedClass p hpk _).trans
      ((smallLogUnit_log p hpk z hz).trans (saturatedImageLog_saturatedExp p hpk z).symm)
  rw [smallLogIntegralLift, LocalKummer.Rational.standardMap_integralUnitClass]
  exact congrArg Subtype.val he

theorem integralLift_of_saturatedLog_small
    (x : saturatedKummerPadicSubmodule (k := k) (Ω := Ω) p hpk)
    (hx : ‖saturatedPadicLog p hpk x‖ ≤ ‖2 * (p : k)‖) :
    ∃ y : HI, LocalKummer.Rational.standardMap p y = (x : HQ) := by
  refine ⟨smallLogIntegralLift p hpk (saturatedPadicLog p hpk x) hx, ?_⟩
  rw [smallLogIntegralLift_standardMap]
  exact congrArg Subtype.val (saturatedExp_saturatedImageLog p hpk ⟨x.1, x.2⟩)

theorem paperNormalizedLog_mem_principalLogImage_of_small {y : k}
    (hy : ‖y‖ ≤ ‖2 * (p : k)‖) : paperNormalizedLog p y ∈ principalLogImage p hpk := by
  have hy1 : ‖y‖ ≤ 1 := hy.trans (norm_two_mul_lt_one hpk).le
  exact smallBall_subset_integralLogSubmodule p hpk (by
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_paperNormalizedLog (Fact.out : p.Prime) hpk hy1] using hy)

end
end JoshiTeich.Act1Scene1.LocalPadicLog
