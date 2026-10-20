import ArithmeticTeichmullerSpaces.Act1Scene1.AdicExponential
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaDeRhamEmbedding

/-!
source-id: JT-SCENE1-INITIAL-THETA-ADDITIVE-TATE-PERIOD
source: Joshi II eq:tate-module-of-lubin-tate and pr:teichmuller-lift-A
(935--958), with the multiplicative formal group.
fidelity: proves the formal-group logarithm law in the original B_dR+,
and turns the original actual Tate logarithm into an injective additive
homomorphism to the original theta kernel. No additivity certificate,
alternative Tate carrier or new period value is input. Topological/Z_p
linearity, Frobenius-p and the paper B/rho identification remain open.
Original proofs; Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaAdditiveTatePeriod

open JoshiTeich.Prologue InitialThetaDeRhamCompletion InitialThetaDeRhamLogarithm
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem logOneAdd_mul (a b : Ring D w) (ha : theta D w a = 0) (hb : theta D w b = 0) :
    logOneAdd D w (a + b + a * b) (by simp only [map_add, map_mul, ha, hb, zero_add, zero_mul]) =
      logOneAdd D w a ha + logOneAdd D w b hb := by
  have hA := AdicExponential.hasEval_log (Ring D w) a (hasEval_kernel D w a ha)
  have hB := AdicExponential.hasEval_log (Ring D w) b (hasEval_kernel D w b hb)
  have he : AdicExponential.exp (Ring D w)
      (AdicLogarithm.oneAdd (Ring D w) a (hasEval_kernel D w a ha) +
        AdicLogarithm.oneAdd (Ring D w) b (hasEval_kernel D w b hb)) (hA.add hB) =
        1 + (a + b + a * b) := by
    rw [AdicExponential.exp_add (Ring D w) _ _ hA hB,
      AdicExponential.exp_log, AdicExponential.exp_log]
    ring
  have h := AdicExponential.log_exp (Ring D w)
    (AdicLogarithm.oneAdd (Ring D w) a (hasEval_kernel D w a ha) +
      AdicLogarithm.oneAdd (Ring D w) b (hasEval_kernel D w b hb)) (hA.add hB)
  simpa only [he, add_sub_cancel_left, logOneAdd] using h

theorem tateCoordinate_mul (x y : InitialThetaCyclotomicTateTilt.Tate D w) :
    tateCoordinate D w (x * y) = tateCoordinate D w x + tateCoordinate D w y +
      tateCoordinate D w x * tateCoordinate D w y := by
  unfold tateCoordinate
  rw [InitialThetaCyclotomicTateTilt.kernelCoordinate_mul, map_add, map_add, map_mul]

theorem tateLog_mul (x y : InitialThetaCyclotomicTateTilt.Tate D w) :
    tateLog D w (x * y) = tateLog D w x + tateLog D w y := by
  simpa only [tateLog, tateCoordinate_mul] using
    logOneAdd_mul D w (tateCoordinate D w x) (tateCoordinate D w y)
      (theta_tateCoordinate D w x) (theta_tateCoordinate D w y)

/-- The original inverse-limit group, with its group operation written additively. -/
def tateLogHom : Additive (InitialThetaCyclotomicTateTilt.Tate D w) →+ Ring D w where
  toFun x := tateLog D w x.toMul
  map_zero' := (InitialThetaDeRhamEmbedding.tateLog_eq_zero_iff D w 1).mpr rfl
  map_add' x y := tateLog_mul D w x.toMul y.toMul

theorem tateLogHom_injective : Function.Injective (tateLogHom D w) := by
  intro x y h
  have hz : tateLogHom D w (x - y) = 0 := by rw [map_sub, h, sub_self]
  have ht := (InitialThetaDeRhamEmbedding.tateLog_eq_zero_iff D w _).mp hz
  have he : x - y = 0 := congrArg Additive.ofMul ht
  exact sub_eq_zero.mp he

/-- The same values in the original additive theta kernel, not a new period carrier. -/
def tateLogKernelHom : Additive (InitialThetaCyclotomicTateTilt.Tate D w) →+
    RingHom.ker (theta D w) where
  toFun x := ⟨tateLogHom D w x, theta_tateLog D w x.toMul⟩
  map_zero' := Subtype.ext (map_zero (tateLogHom D w))
  map_add' x y := Subtype.ext (map_add (tateLogHom D w) x y)

theorem tateLogKernelHom_injective : Function.Injective (tateLogKernelHom D w) := by
  intro x y h
  exact tateLogHom_injective D w (congrArg Subtype.val h)

end
end JoshiTeich.Act1Scene1.InitialThetaAdditiveTatePeriod
