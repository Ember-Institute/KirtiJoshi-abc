import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittScalarPrimeScaling

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-PADIC-SCALAR-NORM
source: Joshi II `se:ff-rings`, the rho norms and Q_p scalar action
on the period algebra; PadicInt.unitCoeff_spec and fraction-ring surj.
fidelity: computes the exact rho norm of a nonzero integral scalar
as rho raised to its integral valuation. Proves exact homogeneity for
every Q_p scalar on each radius completion using one integral numerator
and nonzero denominator. Transfers homogeneity to the common ring's
coordinate seminorms. No multiplicative norm law is supplied as input.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; multiplicativity for arbitrary period-ring
elements, Tate-log eigenspace and paper B/BK identities remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittPadicScalarNorm

open JoshiTeich.Prologue
open InitialThetaBoundedWittPadicScalars InitialThetaWittAllRadiusPadicScalars
open InitialThetaWittPadicScalarContinuity InitialThetaWittScalarPrimeScaling
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem integralMap_unit_factor (ρ : Radius) (a : PadicInt (Arithmetic.residueChar w.1))
    (ha : a ≠ 0) :
    integralMap D w ρ a = integralMap D w ρ (PadicInt.unitCoeff ha) *
      (Arithmetic.residueChar w.1 : Completed D w ρ) ^ a.valuation := by
  have h := congrArg (integralMap D w ρ) (PadicInt.unitCoeff_spec ha)
  simpa only [map_mul, map_pow, map_natCast] using h

theorem norm_integralMap (ρ : Radius) (a : PadicInt (Arithmetic.residueChar w.1)) (ha : a ≠ 0) :
    ‖integralMap D w ρ a‖ = ρ.val.toReal ^ a.valuation := by
  rw [integralMap_unit_factor D w ρ a ha, norm_mul_prime_pow, norm_integral_unit, mul_one]

theorem norm_integralMap_mul (ρ : Radius) (a : PadicInt (Arithmetic.residueChar w.1))
    (x : Completed D w ρ) : ‖integralMap D w ρ a * x‖ = ‖integralMap D w ρ a‖ * ‖x‖ := by
  by_cases ha : a = 0
  · simp only [ha, map_zero, zero_mul, norm_zero]
  · rw [integralMap_unit_factor D w ρ a ha, mul_assoc, norm_integral_unit_mul,
      mul_comm ((Arithmetic.residueChar w.1 : Completed D w ρ) ^ a.valuation) x,
      norm_mul_prime_pow, norm_mul_prime_pow, norm_integral_unit, mul_one]

theorem completedPadicMap_injective (ρ : Radius) : Function.Injective (completedPadicMap D w ρ) :=
  (InitialThetaWittRhoCompletion.inclusion_injective D w ρ).comp (padicMap_injective D w)

theorem integralMap_ne_zero (ρ : Radius) (a : PadicInt (Arithmetic.residueChar w.1)) (ha : a ≠ 0) :
    integralMap D w ρ a ≠ 0 := by
  intro hz
  apply ha
  apply IsFractionRing.injective (PadicInt (Arithmetic.residueChar w.1)) (Padic (Arithmetic.residueChar w.1))
  apply completedPadicMap_injective D w ρ
  exact hz.trans (map_zero _).symm

theorem norm_completedPadicMap_mul (ρ : Radius) (a : Padic (Arithmetic.residueChar w.1))
    (x : Completed D w ρ) : ‖completedPadicMap D w ρ a * x‖ = ‖completedPadicMap D w ρ a‖ * ‖x‖ := by
  obtain ⟨⟨b, c⟩, hc⟩ := IsLocalization.surj
    (nonZeroDivisors (PadicInt (Arithmetic.residueChar w.1))) a
  have hc0 : (c.val : PadicInt (Arithmetic.residueChar w.1)) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp c.property
  have hrel : completedPadicMap D w ρ a * integralMap D w ρ c.val = integralMap D w ρ b := by
    simpa only [map_mul, integralMap, RingHom.comp_apply] using congrArg (completedPadicMap D w ρ) hc
  apply mul_right_cancel₀ (norm_pos_iff.mpr (integralMap_ne_zero D w ρ c.val hc0)).ne'
  calc
    ‖completedPadicMap D w ρ a * x‖ * ‖integralMap D w ρ c.val‖ =
        ‖integralMap D w ρ c.val * (completedPadicMap D w ρ a * x)‖ := by
      rw [norm_integralMap_mul, mul_comm]
    _ = ‖integralMap D w ρ b * x‖ := by
      rw [← mul_assoc, mul_comm (integralMap D w ρ c.val) (completedPadicMap D w ρ a), hrel]
    _ = ‖integralMap D w ρ b‖ * ‖x‖ := norm_integralMap_mul D w ρ b x
    _ = (‖completedPadicMap D w ρ a‖ * ‖integralMap D w ρ c.val‖) * ‖x‖ := by
      rw [← hrel, mul_comm (completedPadicMap D w ρ a) (integralMap D w ρ c.val),
        norm_integralMap_mul, mul_comm ‖integralMap D w ρ c.val‖ ‖completedPadicMap D w ρ a‖]
    _ = (‖completedPadicMap D w ρ a‖ * ‖x‖) * ‖integralMap D w ρ c.val‖ := by ring

theorem norm_padic_smul (ρ : Radius) (a : Padic (Arithmetic.residueChar w.1)) (x : Completed D w ρ) :
    ‖a • x‖ = ‖completedPadicMap D w ρ a‖ * ‖x‖ := norm_completedPadicMap_mul D w ρ a x

theorem norm_completedPadicMap_mul_scalar (ρ : Radius)
    (a b : Padic (Arithmetic.residueChar w.1)) :
    ‖completedPadicMap D w ρ (a * b)‖ =
      ‖completedPadicMap D w ρ a‖ * ‖completedPadicMap D w ρ b‖ := by
  rw [map_mul, norm_completedPadicMap_mul]

theorem norm_completedPadicMap_of_fraction (ρ : Radius)
    (a : Padic (Arithmetic.residueChar w.1)) (b c : PadicInt (Arithmetic.residueChar w.1))
    (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a * algebraMap _ (Padic (Arithmetic.residueChar w.1)) c =
      algebraMap _ (Padic (Arithmetic.residueChar w.1)) b) :
    ‖completedPadicMap D w ρ a‖ = ρ.val.toReal ^ b.valuation / ρ.val.toReal ^ c.valuation := by
  have hrel : completedPadicMap D w ρ a * integralMap D w ρ c = integralMap D w ρ b := by
    simpa only [map_mul, integralMap, RingHom.comp_apply] using congrArg (completedPadicMap D w ρ) h
  have hn := congrArg norm hrel
  rw [mul_comm (completedPadicMap D w ρ a) (integralMap D w ρ c), norm_integralMap_mul,
    norm_integralMap D w ρ b hb, norm_integralMap D w ρ c hc] at hn
  have hp : ρ.val.toReal ^ c.valuation ≠ 0 := by
    rw [← norm_integralMap D w ρ c hc]
    exact (norm_pos_iff.mpr (integralMap_ne_zero D w ρ c hc)).ne'
  exact (eq_div_iff hp).mpr (by simpa only [mul_comm] using hn)

theorem coordinateSeminorm_smul (ρ : Radius) (a : Padic (Arithmetic.residueChar w.1))
    (x : Carrier D w) :
    InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ (a • x) =
      ‖completedPadicMap D w ρ a‖ * InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ x := by
  change ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ (a • x)‖ =
    ‖completedPadicMap D w ρ a‖ * ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ x‖
  rw [evaluate_smul, norm_padic_smul]

end
end JoshiTeich.Act1Scene1.InitialThetaWittPadicScalarNorm
