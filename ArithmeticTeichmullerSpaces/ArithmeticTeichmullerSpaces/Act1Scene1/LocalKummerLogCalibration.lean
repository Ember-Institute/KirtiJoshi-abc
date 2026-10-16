import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerNormalizedIntegralLog
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerSmallLogLift

/-!
source-id: JT-SCENE1-KUMMER-LOG-CALIBRATION
source: ordinary small-ball log/exponential comparison and p-power
denominator clearing; Joshi III 3212--3226.
fidelity: a Q_p-linear map on the original saturated H1 space that sends
every small-log Kummer class to its ordinary log is uniquely the original
ordinary logarithm. A linear exponential with that small-ball formula has
this inverse. Dividing log by pStar fails the same calibration.
boundary: Scene1/Derived; this is a conditional normalization test, not a
construction of period rings, H1e or the BK exponential.
-/

namespace JoshiTeich.Act1Scene1.LocalPadicLog
open Filter Topology
open scoped Valued
universe u v
noncomputable section
variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
variable [CharZero k] [CompleteSpace k] (p : ℕ) [Fact p.Prime]
variable (hpk : ‖(p : k)‖ < 1)
variable [Algebra ℚ_[p] k] [ContinuousSMul ℚ_[p] k]
variable {Ω : Type v} [Field Ω] [Algebra k Ω] [IsGalois k Ω] [Algebra.IsIntegral k Ω]
variable [CharZero Ω] [IsAlgClosed Ω]
local notation "S" => saturatedKummerPadicSubmodule (k := k) (Ω := Ω) p hpk

theorem linearLog_eq_of_smallLog_calibration (L : S →ₗ[ℚ_[p]] k)
    (hL : ∀ (z : k) (hz : ‖z‖ ≤ ‖2 * (p : k)‖),
      L (principalSaturatedClass p hpk (Additive.ofMul (smallLogUnit p hpk z hz))) = z) :
    L = saturatedPadicLog p hpk := by
  ext x
  let z := saturatedPadicLog p hpk x
  have ht : Tendsto (fun n : ℕ => ‖(p : k) ^ n * z‖) atTop (𝓝 0) := by
    simpa only [zero_mul, norm_zero] using
      ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hpk).mul_const z).norm
  have hr : 0 < ‖2 * (p : k)‖ := norm_pos_iff.mpr
    (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))
  obtain ⟨n, hn⟩ := ((tendsto_order.mp ht).2 _ hr).exists
  have he : principalSaturatedClass (Ω := Ω) p hpk
      (Additive.ofMul (smallLogUnit p hpk ((p : k) ^ n * z) hn.le)) = (p : ℚ_[p]) ^ n • x := by
    apply (saturatedPadicLogEquiv p hpk).injective
    change saturatedPadicLog p hpk _ = saturatedPadicLog p hpk _
    rw [saturatedPadicLog_principalSaturatedClass]
    simp only [toMul_ofMul]
    rw [smallLogUnit_log, map_smul]
    simp only [Algebra.smul_def, map_pow, map_natCast, z]
  have h := hL ((p : k) ^ n * z) hn.le
  rw [he, map_smul] at h
  have hm : (p : k) ^ n * L x = (p : k) ^ n * saturatedPadicLog p hpk x := by
    simpa only [Algebra.smul_def, map_pow, map_natCast, z] using h
  exact mul_left_cancel₀ (pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) hm

theorem linearExp_inverse_eq_of_smallLog_calibration (E : k ≃ₗ[ℚ_[p]] S)
    (hE : ∀ (z : k) (hz : ‖z‖ ≤ ‖2 * (p : k)‖),
      E z = principalSaturatedClass p hpk (Additive.ofMul (smallLogUnit p hpk z hz))) :
    E.symm.toLinearMap = saturatedPadicLog p hpk := by
  apply linearLog_eq_of_smallLog_calibration p hpk E.symm.toLinearMap
  intro z hz
  change E.symm _ = z
  rw [← hE z hz]
  exact E.symm_apply_apply z

def normalizedRationalLog : S →ₗ[ℚ_[p]] k :=
  (paperScale p : ℚ_[p])⁻¹ • saturatedPadicLog p hpk

theorem normalizedRationalLog_apply (x : S) :
    normalizedRationalLog p hpk x = (paperScale p : k)⁻¹ * saturatedPadicLog p hpk x := by
  simp only [normalizedRationalLog, LinearMap.smul_apply, Algebra.smul_def, map_inv₀, map_natCast]

theorem normalizedRationalLog_ne_ordinary :
    normalizedRationalLog (Ω := Ω) p hpk ≠ saturatedPadicLog p hpk := by
  intro h
  let x := (saturatedPadicLogEquiv (Ω := Ω) p hpk).symm 1
  have hx : saturatedPadicLog p hpk x = 1 := (saturatedPadicLogEquiv p hpk).apply_symm_apply 1
  have he := LinearMap.congr_fun h x
  rw [normalizedRationalLog_apply, hx, mul_one] at he
  have hc : (paperScale p : k) = 1 := inv_eq_one.mp he
  have hn := (norm_paperScale_eq_norm_two_mul (Fact.out : p.Prime) hpk).trans_lt
    (norm_two_mul_lt_one hpk)
  rw [hc, norm_one] at hn
  exact (lt_irrefl (1 : ℝ)) hn

theorem normalizedRationalLog_fails_smallLog_calibration :
    ¬ (∀ (z : k) (hz : ‖z‖ ≤ ‖2 * (p : k)‖),
      normalizedRationalLog (Ω := Ω) p hpk
        (principalSaturatedClass p hpk (Additive.ofMul (smallLogUnit p hpk z hz))) = z) := by
  intro h
  exact normalizedRationalLog_ne_ordinary p hpk
    (linearLog_eq_of_smallLog_calibration p hpk _ h)

end
end JoshiTeich.Act1Scene1.LocalPadicLog
