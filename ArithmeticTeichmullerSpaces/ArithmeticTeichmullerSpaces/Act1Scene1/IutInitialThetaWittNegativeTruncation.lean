import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittGeometricInterpolation
import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedTruncation

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-NEGATIVE-TRUNCATION
source: Joshi II `se:ff-rings`, the bounded Witt source, its rho norms
and the integral representative problem in `pr:teichmuller-lift-A/B`.
fidelity: every original bounded source element admits an original
bounded source approximation with no negative p-powers. Its image is an
actual Witt vector over the original tilt field. Simultaneously for all
0<s<=r<1, the error has r-norm at most (s/r) times the original s-norm.
The construction removes the finite negative head of one proved genuine
bounded expansion; the estimate includes actual Witt carries.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; the recovered Witt vector need not have
integral tilt coefficients. Completed coefficient recovery, annular
integral representatives and full Tate-kernel classification remain open.
Original carriers and Prologue R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittNegativeTruncation

open JoshiTeich.Prologue InitialThetaBoundedWittExpansion
open WittTeichmullerExpansion
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Radius := InitialThetaWittRhoCompletion.Radius

private theorem negative_monomial_bound (s r c : ℝ) (hs : 0 < s) (hr : 0 < r)
    (hsr : s ≤ r) (hc : 0 ≤ c) (i m : ℕ) (him : i < m) :
    c * r ^ i / r ^ m ≤ (s / r) * (c * s ^ i / s ^ m) := by
  have hratio (t : ℝ) (ht : 0 < t) : c * t ^ i / t ^ m = c / t ^ (m - i) := by
    rw [mul_div_assoc, GeometricInterpolation.powerRatio_eq_zpow t ht,
      show (i : ℤ) - (m : ℤ) = -((m - i : ℕ) : ℤ) by omega,
      zpow_neg, zpow_natCast, ← div_eq_mul_inv]
  rw [hratio r hr, hratio s hs]
  have hq0 : 0 ≤ s / r := (div_pos hs hr).le
  have hq1 : s / r ≤ 1 := (div_le_one hr).mpr hsr
  have hpow : (s / r) ^ (m - i) ≤ s / r := by
    simpa only [pow_one] using pow_le_pow_of_le_one hq0 hq1 (by omega : 1 ≤ m - i)
  calc
    c / r ^ (m - i) = (c / s ^ (m - i)) * (s / r) ^ (m - i) := by
      rw [div_pow]
      field_simp
    _ ≤ (c / s ^ (m - i)) * (s / r) :=
      mul_le_mul_of_nonneg_left hpow (div_nonneg hc (pow_nonneg hs.le _))
    _ = _ := mul_comm _ _

theorem negative_head_norm_bound
    (x n : InitialThetaBoundedWittLocalization.Ring D w) (m : ℕ) (y : FieldWitt D w)
    (C : ℝ) (hC : 0 < C)
    (hbound : ∀ i : ℕ, ‖digits (Arithmetic.residueChar w.1) y i‖ ≤ C)
    (hx : toAmbient D w x * (Arithmetic.residueChar w.1 : Ambient D w) ^ m =
      algebraMap (FieldWitt D w) (Ambient D w) y)
    (hn : toAmbient D w n * (Arithmetic.residueChar w.1 : Ambient D w) ^ m =
      algebraMap (FieldWitt D w) (Ambient D w) (WittVector.init m y))
    (s r : Radius) (hsr : s.val ≤ r.val) :
    InitialThetaWittRhoNorm.realValue D w r.val n ≤
      (s.val.toReal / r.val.toReal) * InitialThetaWittRhoNorm.realValue D w s.val x := by
  by_cases hn0 : n = 0
  · rw [hn0, InitialThetaWittRhoNorm.realValue_zero D w r.val r.property.1.ne' r.property.2.le]
    exact mul_nonneg (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (InitialThetaWittRhoNorm.realValue_nonneg D w s.val x)
  have hb (i : ℕ) : ‖digits (Arithmetic.residueChar w.1) (WittVector.init m y) i‖ ≤ C := by
    rw [WittWeightedTruncation.digits_init]
    split_ifs
    · exact hbound i
    · simpa only [norm_zero] using hC.le
  have hy0 : WittVector.init m y ≠ 0 := by
    intro h
    apply hn0
    apply toAmbient_injective D w
    rw [map_zero]
    rw [h, map_zero] at hn
    exact (mul_eq_zero.mp hn).resolve_right (pow_ne_zero m
      (WittVector.FractionRing.p_nonzero (Arithmetic.residueChar w.1) (InitialThetaTiltField.Carrier D w)))
  obtain ⟨i, hi, _, _⟩ := WittWeightedDigitMaximum.exists_first_max
    (Arithmetic.residueChar w.1) r.val r.property.2 (WittVector.init m y) C hb
  have hdi := WittWeightedDigitMaximum.maximizing_digit_ne_zero
    (Arithmetic.residueChar w.1) r.val r.property.1.ne' _ hy0 i hi
  have him : i < m := by
    by_contra h
    rw [WittWeightedTruncation.digits_init, if_neg h] at hdi
    exact hdi rfl
  have hnorm : InitialThetaWittRhoNorm.realValue D w r.val n =
      ‖digits (Arithmetic.residueChar w.1) y i‖ * r.val.toReal ^ i / r.val.toReal ^ m := by
    rw [InitialThetaWittRhoNorm.realValue,
      InitialThetaWittRhoValue.value_eq_of_presentation D w r.val r.property.1.ne'
        (r.property.2.trans ENNReal.one_lt_top).ne n m _ hn,
      hi, ENNReal.toReal_div, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_pow, ENNReal.toReal_pow,
      WittWeightedTruncation.digits_init, if_pos him]
  rw [hnorm]
  have hs : 0 < s.val.toReal := ENNReal.toReal_pos s.property.1.ne'
    (s.property.2.trans ENNReal.one_lt_top).ne
  have hr : 0 < r.val.toReal := ENNReal.toReal_pos r.property.1.ne'
    (r.property.2.trans ENNReal.one_lt_top).ne
  have hsr' := (ENNReal.toReal_le_toReal (s.property.2.trans ENNReal.one_lt_top).ne
    (r.property.2.trans ENNReal.one_lt_top).ne).mpr hsr
  exact (negative_monomial_bound _ _ _ hs hr hsr' (norm_nonneg _) i m him).trans
    (mul_le_mul_of_nonneg_left
      (InitialThetaWittGeometricInterpolation.dividedTerm_le_realValue D w s x m y hx i)
        (div_nonneg hs.le hr.le))

theorem exists_nonnegative_approximation
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    ∃ a : InitialThetaBoundedWittLocalization.Ring D w, ∃ b : FieldWitt D w,
      toAmbient D w a = algebraMap (FieldWitt D w) (Ambient D w) b ∧
      ∀ s r : Radius, s.val ≤ r.val →
        InitialThetaWittRhoNorm.realValue D w r.val (x - a) ≤
          (s.val.toReal / r.val.toReal) * InitialThetaWittRhoNorm.realValue D w s.val x := by
  obtain ⟨m, y, c, C, hC, hbound, hc, hx⟩ := hasBoundedExpansion D w x
  have hd := digits_unique (Arithmetic.residueChar w.1) y c hc
  have hb (i : ℕ) : ‖digits (Arithmetic.residueChar w.1) y i‖ ≤ C := by
    rw [← congrFun hd i]
    exact hbound i
  have hinit (i : ℕ) : ‖digits (Arithmetic.residueChar w.1) (WittVector.init m y) i‖ ≤ C := by
    rw [WittWeightedTruncation.digits_init]
    split_ifs
    · exact hb i
    · simpa only [norm_zero] using hC.le
  have hp : (Arithmetic.residueChar w.1 : Ambient D w) ^ m ≠ 0 := pow_ne_zero m
    (WittVector.FractionRing.p_nonzero (Arithmetic.residueChar w.1) (InitialThetaTiltField.Carrier D w))
  let z : Ambient D w := algebraMap (FieldWitt D w) (Ambient D w) (WittVector.init m y) /
    (Arithmetic.residueChar w.1 : Ambient D w) ^ m
  have hz : z * (Arithmetic.residueChar w.1 : Ambient D w) ^ m =
      algebraMap (FieldWitt D w) (Ambient D w) (WittVector.init m y) := div_mul_cancel₀ _ hp
  obtain ⟨n, hn⟩ := mem_range_of_hasBoundedExpansion D w z
    ⟨m, WittVector.init m y, digits (Arithmetic.residueChar w.1) (WittVector.init m y),
      C, hC, hinit, expands_digits _ _, hz⟩
  have hnp : toAmbient D w n * (Arithmetic.residueChar w.1 : Ambient D w) ^ m =
      algebraMap (FieldWitt D w) (Ambient D w) (WittVector.init m y) := by rw [hn]; exact hz
  have htail : (Arithmetic.residueChar w.1 : FieldWitt D w) ^ m ∣ WittVector.tail m y := by
    apply Ideal.mem_span_singleton.mp
    apply (WittVector.mem_span_p_pow_iff_le_coeff_eq_zero _ m).mpr
    intro i hi
    simp only [WittVector.tail, WittVector.select, WittVector.coeff_mk, if_neg (not_le.mpr hi)]
  obtain ⟨b, hb'⟩ := htail
  refine ⟨x - n, b, ?_, ?_⟩
  · apply mul_right_cancel₀ hp
    calc
      _ = algebraMap (FieldWitt D w) (Ambient D w) (y - WittVector.init m y) := by
        rw [map_sub, sub_mul, hx, hnp, map_sub]
      _ = algebraMap (FieldWitt D w) (Ambient D w) (WittVector.tail m y) := by
        congr 1
        exact sub_eq_iff_eq_add.mpr ((WittVector.init_add_tail y m).symm.trans (add_comm _ _))
      _ = _ := by rw [hb', map_mul, map_pow, map_natCast, mul_comm]
  · intro s r hsr
    rw [sub_sub_cancel]
    exact negative_head_norm_bound D w x n m y C hC hb hx hnp s r hsr

end
end JoshiTeich.Act1Scene1.InitialThetaWittNegativeTruncation
