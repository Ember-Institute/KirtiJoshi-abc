import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittRhoNorm
import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedMultiplicativity
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittAllRadiusCompletion

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-RHO-MULTIPLICATIVE-NORM
source: Joshi II `se:ff-rings`, the original weighted Teichmuller value on
the independently constructed standard p-only bounded Witt localization.
fidelity: proves exact multiplicativity of the original rho value from
bounded numerator presentations, then transports it to fixed-radius
completions and all-radius coordinate seminorms.
Original proofs; no reference implementation copied.
boundary: this proves multiplicativity for the standard p-only carriers; it
does not identify them with paper B or assert period/BK identities.
-/

namespace JoshiTeich.Act1Scene1.PadicWittRhoMultiplicativeNorm

open scoped ENNReal
noncomputable section
variable (p : ℕ) [Fact p.Prime]

private theorem exists_bounded_digit_presentation
    (x : PadicBoundedWittLocalization.Ring p) :
    ∃ m : ℕ, ∃ y : PadicBoundedWittExpansion.FieldWitt p, ∃ C : ℝ,
      (∀ n, ‖WittTeichmullerExpansion.digits p y n‖ ≤ C) ∧
      PadicBoundedWittExpansion.toAmbient p x *
          (p : PadicBoundedWittExpansion.Ambient p) ^ m =
        algebraMap _ _ y := by
  obtain ⟨m, y, hrel, hfinite⟩ :=
    PadicBoundedWittExpansion.toAmbient_exists_finite_value p 1 le_rfl x
  let C : ℝ := (WittWeightedDigits.value p 1 y).toReal
  refine ⟨m, y, C, ?_, hrel⟩
  intro n
  have hterm := WittWeightedDigits.term_le_value p 1 y n
  simp only [one_pow, mul_one] at hterm
  have hvalue : WittWeightedDigits.value p 1 y = ENNReal.ofReal C := by
    exact (ENNReal.ofReal_toReal hfinite.ne).symm
  rw [hvalue] at hterm
  have hC_nonneg : 0 ≤ C := ENNReal.toReal_nonneg
  exact (ENNReal.ofReal_le_ofReal_iff hC_nonneg).mp hterm

theorem value_mul (ρ : PadicWittRhoCompletion.Radius)
    (x y : PadicBoundedWittLocalization.Ring p) :
    PadicWittRhoValue.value p ρ.val (x * y) =
      PadicWittRhoValue.value p ρ.val x * PadicWittRhoValue.value p ρ.val y := by
  obtain ⟨m, a, C, hC, ha⟩ := exists_bounded_digit_presentation p x
  obtain ⟨n, b, E, hE, hb⟩ := exists_bounded_digit_presentation p y
  have hρtop : ρ.val ≠ ⊤ := (ρ.property.2.trans ENNReal.one_lt_top).ne
  have he : PadicBoundedWittExpansion.toAmbient p (x * y) *
      (p : PadicBoundedWittExpansion.Ambient p) ^ (m + n) =
      algebraMap (PadicBoundedWittExpansion.FieldWitt p)
        (PadicBoundedWittExpansion.Ambient p) (a * b) := by
    rw [map_mul, map_mul, pow_add]
    calc
      _ = (PadicBoundedWittExpansion.toAmbient p x *
          (p : PadicBoundedWittExpansion.Ambient p) ^ m) *
          (PadicBoundedWittExpansion.toAmbient p y *
          (p : PadicBoundedWittExpansion.Ambient p) ^ n) :=
        mul_mul_mul_comm _ _ _ _
      _ = _ := by rw [ha, hb]
  have haBound : ∀ k, ‖WittTeichmullerExpansion.digits p a k‖ ≤ C := by
    exact hC
  have hbBound : ∀ k, ‖WittTeichmullerExpansion.digits p b k‖ ≤ E := by
    exact hE
  rw [PadicWittRhoValue.value_eq_of_presentation p ρ.val ρ.property.1.ne' hρtop _
      (m + n) (a * b) he,
    PadicWittRhoValue.value_eq_of_presentation p ρ.val ρ.property.1.ne' hρtop x m a ha,
    PadicWittRhoValue.value_eq_of_presentation p ρ.val ρ.property.1.ne' hρtop y n b hb,
    WittWeightedMultiplicativity.value_mul p
      (LocalGeometricFontaine.integerRing (PadicTiltField.Carrier p))
      (LocalGeometricFontaine.mem_integerRing (PadicTiltField.Carrier p))
      ρ.val ρ.property.1.ne' ρ.property.2 a b C E haBound hbBound]
  simp only [div_eq_mul_inv, ENNReal.inv_pow]
  rw [pow_add]
  exact mul_mul_mul_comm
    (WittWeightedDigits.value p ρ.val a)
    (WittWeightedDigits.value p ρ.val b)
    ((ρ.val⁻¹) ^ m) ((ρ.val⁻¹) ^ n)

theorem realValue_mul (ρ : PadicWittRhoCompletion.Radius)
    (x y : PadicBoundedWittLocalization.Ring p) :
    PadicWittRhoNorm.realValue p ρ.val (x * y) =
      PadicWittRhoNorm.realValue p ρ.val x * PadicWittRhoNorm.realValue p ρ.val y := by
  exact (congrArg ENNReal.toReal (value_mul p ρ x y)).trans ENNReal.toReal_mul

def mulRingNorm (ρ : PadicWittRhoCompletion.Radius) :
    MulRingNorm (PadicBoundedWittLocalization.Ring p) where
  __ := (PadicWittRhoNorm.ringNorm p ρ.val ρ.property.1.ne' ρ.property.2.le).toAddGroupNorm
  map_one' := PadicWittRhoNorm.realValue_one p ρ.val ρ.property.1.ne' ρ.property.2.le
  map_mul' := realValue_mul p ρ

instance sourceNormMul (ρ : PadicWittRhoCompletion.Radius) :
    NormMulClass (PadicWittRhoCompletion.Source p ρ) where
  norm_mul x y := realValue_mul p ρ x y

instance completedNormMul (ρ : PadicWittRhoCompletion.Radius) :
    NormMulClass (PadicWittRhoCompletion.Completed p ρ) where
  norm_mul x y := by
    refine (PadicWittRhoCompletion.inclusion_denseRange p ρ).induction_on₂
      (p := fun a b : PadicWittRhoCompletion.Completed p ρ =>
        ‖a * b‖ = ‖a‖ * ‖b‖)
      (isClosed_eq
        (continuous_fst.mul continuous_snd).norm
        (continuous_fst.norm.mul continuous_snd.norm)) ?_ x y
    intro a b
    rw [← map_mul, PadicWittRhoCompletion.inclusion_norm,
      PadicWittRhoCompletion.inclusion_norm, PadicWittRhoCompletion.inclusion_norm]
    exact realValue_mul p ρ a b

theorem coordinateSeminorm_mul (ρ : PadicWittAllRadiusCompletion.Radius)
    (x y : PadicWittAllRadiusCompletion.Carrier p) :
    PadicWittAllRadiusCompletion.coordinateSeminorm p ρ (x * y) =
      PadicWittAllRadiusCompletion.coordinateSeminorm p ρ x *
        PadicWittAllRadiusCompletion.coordinateSeminorm p ρ y := by
  change ‖PadicWittAllRadiusCompletion.evaluate p ρ (x * y)‖ =
    ‖PadicWittAllRadiusCompletion.evaluate p ρ x‖ *
      ‖PadicWittAllRadiusCompletion.evaluate p ρ y‖
  rw [map_mul, norm_mul]

end
end JoshiTeich.Act1Scene1.PadicWittRhoMultiplicativeNorm
