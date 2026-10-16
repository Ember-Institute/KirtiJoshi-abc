import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerSaturatedLogarithm
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalPadicLogBall

/-!
source-id: JT-SCENE1-SATURATED-KUMMER-LOG-EQUIVALENCE
source: small-ball ordinary logarithm surjectivity and rational Kummer
p-power division; Joshi III 3212--3226, ss:bloch-kato-exp/logarithm.
fidelity: proves the existing saturated image logarithm is surjective and
constructs an additive equivalence with the actual local field. Its inverse
has the divided-principal-Kummer-class formula. This is an ordinary-log
comparison on an explicitly constructed subgroup of rational H1; H1e/BK
identification, Q_p scalar closure and topological comparison remain open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalPadicLog
open Filter Topology
open scoped Valued
universe u v
noncomputable section
variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
variable [CharZero k] [CompleteSpace k]
variable {Ω : Type v} [Field Ω] [Algebra k Ω] [IsGalois k Ω] [Algebra.IsIntegral k Ω]
variable [CharZero Ω] [IsAlgClosed Ω] (p : ℕ) [Fact p.Prime]
variable (hpk : ‖(p : k)‖ < 1)

include hpk in
/-- Clearing a p-power denominator puts every local element in the log image. -/
theorem exists_prime_power_mul_eq_principalLog (y : k) :
    ∃ (n : ℕ) (a : principalUnits (k := k)),
      padicLog (a.1 : k) = (p : k) ^ n * y := by
  have ht : Tendsto (fun n : ℕ => ‖(p : k) ^ n * y‖) atTop (𝓝 0) := by
    simpa only [zero_mul, norm_zero] using
      ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hpk).mul_const y).norm
  have hr : 0 < ‖2 * (p : k)‖ := norm_pos_iff.mpr
    (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))
  obtain ⟨n, hn⟩ := ((tendsto_order.mp ht).2 ‖2 * (p : k)‖ hr).exists
  obtain ⟨b, hb, hlog⟩ := exists_padicLog_eq (Fact.out : p.Prime) hpk hn.le
  have hb1 : ‖(1 + b : k) - 1‖ < 1 := by
    simpa only [add_sub_cancel_left] using hb.trans_lt (norm_two_mul_lt_one hpk)
  have hunit : (1 + b : k) ≠ 0 := by
    intro hz
    rw [hz, zero_sub, norm_neg, norm_one] at hb1
    exact (lt_irrefl (1 : ℝ)) hb1
  exact ⟨n, ⟨Units.mk0 (1 + b) hunit, hb1⟩, hlog⟩

theorem saturatedImageLog_surjective :
    Function.Surjective (saturatedImageLog (k := k) (Ω := Ω) p hpk) := by
  intro y
  obtain ⟨n, a, ha⟩ := exists_prime_power_mul_eq_principalLog p hpk y
  let b : principalKummerImage (k := k) (Ω := Ω) p :=
    (principalKummerHom (k := k) (Ω := Ω) p).rangeRestrict (Additive.ofMul a)
  refine ⟨saturatedClassOfImage p b n, ?_⟩
  calc
    _ = ((p : k) ^ n)⁻¹ * principalImageLog p hpk b :=
      saturatedImageLog_classOfImage p hpk b n
    _ = ((p : k) ^ n)⁻¹ * padicLog (a.1 : k) :=
      congrArg (((p : k) ^ n)⁻¹ * ·) (principalImageLog_class (Ω := Ω) p hpk (Additive.ofMul a))
    _ = y := by
      rw [ha, inv_mul_cancel_left₀]
      exact pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

/-- The source is the actual p-power saturated subgroup of rational H1. -/
def saturatedLogEquiv : saturatedKummerImage (k := k) (Ω := Ω) p ≃+ k :=
  AddEquiv.ofBijective (saturatedImageLog p hpk)
    ⟨saturatedImageLog_injective p hpk, saturatedImageLog_surjective p hpk⟩

/-- Ordinary exponential comparison, defined as the inverse of the image log. -/
def saturatedExp : k →+ saturatedKummerImage (k := k) (Ω := Ω) p :=
  (saturatedLogEquiv p hpk).symm.toAddMonoidHom

theorem saturatedImageLog_saturatedExp (y : k) :
    saturatedImageLog p hpk (saturatedExp (Ω := Ω) p hpk y) = y :=
  (saturatedLogEquiv p hpk).apply_symm_apply y

theorem saturatedExp_saturatedImageLog (x : saturatedKummerImage (k := k) (Ω := Ω) p) :
    saturatedExp p hpk (saturatedImageLog p hpk x) = x :=
  (saturatedLogEquiv p hpk).symm_apply_apply x

/-- The inverse agrees with division of an actual principal-unit Kummer class. -/
theorem saturatedExp_eq_dividedKummerClass
    (a : principalUnits (k := k)) (n : ℕ) :
    saturatedExp (Ω := Ω) p hpk (((p : k) ^ n)⁻¹ * padicLog (a.1 : k)) =
      saturatedClassOfImage p ((principalKummerHom p).rangeRestrict (Additive.ofMul a)) n := by
  have hlog := (saturatedImageLog_classOfImage p hpk
    ((principalKummerHom (k := k) (Ω := Ω) p).rangeRestrict (Additive.ofMul a)) n).trans
      (congrArg (((p : k) ^ n)⁻¹ * ·) (principalImageLog_class (Ω := Ω) p hpk (Additive.ofMul a)))
  exact saturatedImageLog_injective p hpk
    ((saturatedImageLog_saturatedExp (Ω := Ω) p hpk _).trans hlog.symm)

end
end JoshiTeich.Act1Scene1.LocalPadicLog
