import ArithmeticTeichmullerSpaces.Act1Scene1.PadicHaarScaling
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

/-!
source-id: JT-SCENE1-PADIC-HAAR-SCALAR-NORM
source: actual prime Haar scaling, the p-adic valuation/norm formula, and
the multiplicative Haar character. Norm-one scalars preserve the integral ball.
fidelity: computes the Haar character of every nonzero p-adic scalar as its
actual norm, with image and preimage formulas for arbitrary additive Haar.
No determinant, theta-volume, or paper normalization certificate is assumed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.PadicHaar

open MeasureTheory
open scoped Pointwise ENNReal

noncomputable section
variable {p : ℕ} [Fact p.Prime]

private theorem char_eq_one_of_norm_one (u : ℚ_[p]ˣ) (hu : ‖(u : ℚ_[p])‖ = 1) :
    distribHaarChar ℚ_[p] u = 1 := by
  let μ : Measure ℚ_[p] := Measure.addHaar
  let B : Set ℚ_[p] := Metric.closedBall 0 1
  have hB0 : μ B ≠ 0 :=
    ((IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero).measure_pos μ
      ⟨0, by simp [B]⟩).ne'
  have hBtop : μ B ≠ ⊤ := (isCompact_closedBall _ _).measure_lt_top.ne
  have hball : u • B = B := by
    change (fun x : ℚ_[p] => (u : ℚ_[p]) * x) '' B = B
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
      rw [norm_mul, hu, one_mul]
      exact hx
    · intro hy
      refine ⟨y / (u : ℚ_[p]), ?_, mul_div_cancel₀ y u.ne_zero⟩
      rw [Metric.mem_closedBall, dist_zero_right] at hy ⊢
      simpa only [norm_div, hu, div_one] using hy
  have h := distribHaarChar_mul μ u B
  rw [hball] at h
  have he : (distribHaarChar ℚ_[p] u : ENNReal) = 1 :=
    (ENNReal.mul_left_inj hB0 hBtop).mp (by simpa using h)
  exact ENNReal.coe_injective (by simpa using he)

private theorem char_prime :
    (distribHaarChar ℚ_[p] (Units.mk0 (p : ℚ_[p]) (padic_natCast_ne_zero p)) : ℝ) =
      (p : ℝ)⁻¹ := by
  let μ : Measure ℚ_[p] := Measure.addHaar
  let B : Set ℚ_[p] := Metric.closedBall 0 1
  have hB0 : μ B ≠ 0 :=
    ((IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero).measure_pos μ
      ⟨0, by simp [B]⟩).ne'
  have hBtop : μ B ≠ ⊤ := (isCompact_closedBall _ _).measure_lt_top.ne
  have h := distribHaarChar_mul μ (Units.mk0 (p : ℚ_[p]) (padic_natCast_ne_zero p)) B
  have him := measure_image_smul_padic (p := p) μ (s := B) measurableSet_closedBall
  have hchar : (distribHaarChar ℚ_[p]
      (Units.mk0 (p : ℚ_[p]) (padic_natCast_ne_zero p)) : ENNReal) = (p : ENNReal)⁻¹ := by
    apply (ENNReal.mul_left_inj hB0 hBtop).mp
    simpa only [Module.finrank_self, pow_one, Units.smul_def, smul_eq_mul] using h.trans him
  have hr := congrArg ENNReal.toReal hchar
  simpa using hr

theorem distribHaarChar_eq_norm (a : ℚ_[p]ˣ) :
    (distribHaarChar ℚ_[p] a : ℝ) = ‖(a : ℚ_[p])‖ := by
  let q : ℚ_[p]ˣ := Units.mk0 (p : ℚ_[p]) (padic_natCast_ne_zero p)
  let n : ℤ := (a : ℚ_[p]).valuation
  let u : ℚ_[p]ˣ := a * (q ^ n)⁻¹
  have hanorm : ‖(a : ℚ_[p])‖ = (p : ℝ) ^ (-n) := Padic.norm_eq_zpow_neg_valuation a.ne_zero
  have hqnorm : ‖((q ^ n : ℚ_[p]ˣ) : ℚ_[p])‖ = (p : ℝ) ^ (-n) := by
    simp only [Units.val_zpow_eq_zpow_val, q, Units.val_mk0]
    exact Padic.norm_p_zpow n
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hunorm : ‖(u : ℚ_[p])‖ = 1 := by
    simp only [u, Units.val_mul, Units.val_inv_eq_inv_val]
    rw [norm_mul, norm_inv, hanorm, hqnorm, mul_inv_cancel₀ (zpow_ne_zero _ hp.ne')]
  have hprod : u * q ^ n = a := by simp [u]
  conv_lhs => rw [← hprod]
  rw [map_mul, char_eq_one_of_norm_one u hunorm, one_mul, map_zpow]
  have hqchar : (distribHaarChar ℚ_[p] q : ℝ) = (p : ℝ)⁻¹ := char_prime
  push_cast
  rw [hqchar, inv_zpow, ← zpow_neg, ← hanorm]

theorem measure_image_mul_eq_norm (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure]
    (a : ℚ_[p]) (ha : a ≠ 0) (s : Set ℚ_[p]) :
    μ ((fun x => a * x) '' s) = ENNReal.ofReal ‖a‖ * μ s := by
  have h := distribHaarChar_mul μ (Units.mk0 a ha) s
  have hc : (distribHaarChar ℚ_[p] (Units.mk0 a ha) : ENNReal) = ENNReal.ofReal ‖a‖ := by
    have hr := distribHaarChar_eq_norm (Units.mk0 a ha)
    change (distribHaarChar ℚ_[p] (Units.mk0 a ha) : ℝ) = ‖a‖ at hr
    rw [← hr]
    simp
  rw [hc] at h
  exact h.symm

theorem measure_preimage_mul_eq_inv_norm (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure]
    (a : ℚ_[p]) (ha : a ≠ 0) (s : Set ℚ_[p]) :
    μ ((fun x => a * x) ⁻¹' s) = ENNReal.ofReal ‖a⁻¹‖ * μ s := by
  have he : (fun x : ℚ_[p] => a * x) ⁻¹' s = (fun x => a⁻¹ * x) '' s := by
    ext x
    constructor
    · intro hx
      exact ⟨a * x, hx, inv_mul_cancel_left₀ ha x⟩
    · rintro ⟨y, hy, rfl⟩
      change a * (a⁻¹ * y) ∈ s
      simpa only [mul_inv_cancel_left₀ ha] using hy
  rw [he]
  exact measure_image_mul_eq_norm μ a⁻¹ (inv_ne_zero ha) s

end
end JoshiTeich.Act1Scene1.PadicHaar
