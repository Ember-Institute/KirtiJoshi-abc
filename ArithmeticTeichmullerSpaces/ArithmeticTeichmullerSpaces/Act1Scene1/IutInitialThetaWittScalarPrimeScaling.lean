import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittPadicScalarContinuity

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-SCALAR-PRIME-SCALING
source: Joshi II `se:ff-rings`, the rho norms on the Q_p period algebra.
fidelity: extends the exact original p-shift norm identity to every
element of a fixed-radius completion by density. Proves exact scaling
by p^N and isometry under every actual Z_p unit, using the proved
integral bound on both the unit and its inverse.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; general ring-norm multiplicativity and paper
B/Tate-log/BK identities remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittScalarPrimeScaling

open JoshiTeich.Prologue
open InitialThetaBoundedWittPadicScalars InitialThetaWittAllRadiusPadicScalars
open InitialThetaWittPadicScalarContinuity
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Completed (ρ : Radius) := InitialThetaWittRhoCompletion.Completed D w ρ

def integralMap (ρ : Radius) : PadicInt (Arithmetic.residueChar w.1) →+* Completed D w ρ :=
  (completedPadicMap D w ρ).comp
    (algebraMap (PadicInt (Arithmetic.residueChar w.1)) (Padic (Arithmetic.residueChar w.1)))

theorem norm_integralMap_le_one (ρ : Radius) (a : PadicInt (Arithmetic.residueChar w.1)) :
    ‖integralMap D w ρ a‖ ≤ 1 := norm_completedPadicInt_le_one D w ρ a

theorem realValue_mul_prime (ρ : Radius) (x : InitialThetaBoundedWittLocalization.Ring D w) :
    InitialThetaWittRhoNorm.realValue D w ρ.val (x * Arithmetic.residueChar w.1) =
      ρ.val.toReal * InitialThetaWittRhoNorm.realValue D w ρ.val x := by
  have h := congrArg ENNReal.toReal (InitialThetaWittRhoValue.value_mul_prime D w ρ.val
    ρ.property.1.ne' (ρ.property.2.trans ENNReal.one_lt_top).ne x)
  simpa only [InitialThetaWittRhoNorm.realValue, ENNReal.toReal_mul] using h

theorem norm_mul_prime (ρ : Radius) (x : Completed D w ρ) :
    ‖x * (Arithmetic.residueChar w.1 : Completed D w ρ)‖ = ρ.val.toReal * ‖x‖ := by
  refine (InitialThetaWittRhoCompletion.inclusion_denseRange D w ρ).induction_on
    (p := fun z : Completed D w ρ =>
      ‖z * (Arithmetic.residueChar w.1 : Completed D w ρ)‖ = ρ.val.toReal * ‖z‖) x ?_ ?_
  · exact isClosed_eq (continuous_id.mul continuous_const).norm (continuous_const.mul continuous_norm)
  · intro y
    rw [← map_natCast (InitialThetaWittRhoCompletion.inclusion D w ρ) (Arithmetic.residueChar w.1),
      ← map_mul, InitialThetaWittRhoCompletion.inclusion_norm,
      InitialThetaWittRhoCompletion.inclusion_norm]
    exact realValue_mul_prime D w ρ y

theorem norm_mul_prime_pow (ρ : Radius) (x : Completed D w ρ) (N : ℕ) :
    ‖x * (Arithmetic.residueChar w.1 : Completed D w ρ) ^ N‖ = ρ.val.toReal ^ N * ‖x‖ := by
  induction N with
  | zero => simp only [pow_zero, mul_one, one_mul]
  | succ N ih =>
    rw [pow_succ, ← mul_assoc, norm_mul_prime, ih, pow_succ]
    ring

theorem norm_integral_unit_mul (ρ : Radius) (u : (PadicInt (Arithmetic.residueChar w.1))ˣ)
    (x : Completed D w ρ) : ‖integralMap D w ρ u * x‖ = ‖x‖ := by
  apply le_antisymm
  · exact (norm_mul_le _ _).trans
      ((mul_le_mul_of_nonneg_right (norm_integralMap_le_one D w ρ u) (norm_nonneg x)).trans_eq
        (one_mul ‖x‖))
  · calc
      ‖x‖ = ‖integralMap D w ρ (u⁻¹ : (PadicInt (Arithmetic.residueChar w.1))ˣ) *
          (integralMap D w ρ u * x)‖ := by
        rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
      _ ≤ ‖integralMap D w ρ (u⁻¹ : (PadicInt (Arithmetic.residueChar w.1))ˣ)‖ *
          ‖integralMap D w ρ u * x‖ := norm_mul_le _ _
      _ ≤ 1 * ‖integralMap D w ρ u * x‖ :=
        mul_le_mul_of_nonneg_right (norm_integralMap_le_one D w ρ ↑u⁻¹) (norm_nonneg _)
      _ = _ := one_mul _

theorem norm_integral_unit (ρ : Radius) (u : (PadicInt (Arithmetic.residueChar w.1))ˣ) :
    ‖integralMap D w ρ u‖ = 1 := by
  simpa only [mul_one, norm_one] using norm_integral_unit_mul D w ρ u 1

end
end JoshiTeich.Act1Scene1.InitialThetaWittScalarPrimeScaling
