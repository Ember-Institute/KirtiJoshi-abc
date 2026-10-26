import ArithmeticTeichmullerSpaces.Act1Scene1.PositivePowerCalibration
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittMultiplicativeNorm
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittPadicScalarNorm

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-SCALAR-CALIBRATION
source: Joshi II `se:ff-rings`, the rho norms and the standard Q_p
scalar norm on the Frechet period algebra.
fidelity: the positive power log(|p|_p)/log(rho) takes the original
rho norm of every actual Q_p scalar to its standard p-adic norm.
Integral valuation factorization proves the integral case; the actual
fraction-field presentation proves the general case, including zero.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; normalized seminorms and their topology are
separate consumers. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittScalarCalibration

open JoshiTeich.Prologue InitialThetaWittAllRadiusPadicScalars
open InitialThetaWittPadicScalarNorm InitialThetaWittScalarPrimeScaling
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def exponent (ρ : Radius) : ℝ :=
  PositivePowerCalibration.exponent ρ.val.toReal ‖(Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1))‖

theorem exponent_pos (ρ : Radius) : 0 < exponent D w ρ := by
  apply PositivePowerCalibration.exponent_pos
  · exact ENNReal.toReal_pos ρ.property.1.ne' (ρ.property.2.trans ENNReal.one_lt_top).ne
  · simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (ρ.property.2.trans ENNReal.one_lt_top).ne ENNReal.one_ne_top).mpr ρ.property.2
  · exact norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero)
  · exact Padic.norm_p_lt_one

theorem radius_rpow_exponent (ρ : Radius) :
    ρ.val.toReal ^ exponent D w ρ = ‖(Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1))‖ := by
  apply PositivePowerCalibration.rpow_exponent
  · exact ENNReal.toReal_pos ρ.property.1.ne' (ρ.property.2.trans ENNReal.one_lt_top).ne
  · simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (ρ.property.2.trans ENNReal.one_lt_top).ne ENNReal.one_ne_top).mpr ρ.property.2
  · exact norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero)

theorem integralMap_rpow (ρ : Radius) (a : PadicInt (Arithmetic.residueChar w.1)) :
    ‖integralMap D w ρ a‖ ^ exponent D w ρ = ‖(a : Padic (Arithmetic.residueChar w.1))‖ := by
  by_cases ha : a = 0
  · rw [ha, map_zero, norm_zero, Real.zero_rpow (exponent_pos D w ρ).ne', PadicInt.coe_zero, norm_zero]
  · rw [norm_integralMap D w ρ a ha,
      ← Real.rpow_pow_comm ENNReal.toReal_nonneg (exponent D w ρ) a.valuation,
      radius_rpow_exponent, Padic.norm_p, PadicInt.norm_coe, PadicInt.norm_eq_zpow_neg_valuation ha,
      zpow_neg, zpow_natCast, inv_pow]

theorem completedPadicMap_rpow (ρ : Radius) (a : Padic (Arithmetic.residueChar w.1)) :
    ‖completedPadicMap D w ρ a‖ ^ exponent D w ρ = ‖a‖ := by
  obtain ⟨⟨b, c⟩, hc⟩ := IsLocalization.surj
    (nonZeroDivisors (PadicInt (Arithmetic.residueChar w.1))) a
  have hc0 : (c.val : PadicInt (Arithmetic.residueChar w.1)) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp c.property
  have hcQ : (c.val : Padic (Arithmetic.residueChar w.1)) ≠ 0 := PadicInt.coe_ne_zero.mpr hc0
  have hrel : completedPadicMap D w ρ a * integralMap D w ρ c.val = integralMap D w ρ b := by
    simpa only [map_mul, integralMap, RingHom.comp_apply] using congrArg (completedPadicMap D w ρ) hc
  have hn := congrArg norm hrel
  rw [norm_mul] at hn
  have hp := congrArg (fun t : ℝ => t ^ exponent D w ρ) hn
  rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _), integralMap_rpow, integralMap_rpow] at hp
  have hq : ‖a‖ * ‖(c.val : Padic (Arithmetic.residueChar w.1))‖ =
      ‖(b : Padic (Arithmetic.residueChar w.1))‖ := by
    simpa only [norm_mul, PadicInt.algebraMap_apply] using congrArg norm hc
  exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hcQ) (hp.trans hq.symm)

end
end JoshiTeich.Act1Scene1.InitialThetaWittScalarCalibration
