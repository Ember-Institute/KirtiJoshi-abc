import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittThetaEvaluation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTateLogarithmLinear

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-THETA-TATE-FIBER
source: Joshi II `pr:teichmuller-lift-A`, Teichmuller lifts and their
Tate-module translates under the canonical period-ring evaluation.
fidelity: continuity of the actual evaluation sends the convergent
Tate-log series to zero. The original integral lift gives the prescribed
untilt value and the same norm at every radius. Every translate by the
proved injective Tate-log map remains in that fiber.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; this uses the original untilt of the given
local source. Arbitrary Ansatz points and full kernel identities remain
separate obligations. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittThetaTateFiber

open JoshiTeich.Prologue InitialThetaWittThetaBound InitialThetaWittThetaEvaluation
open InitialThetaWittTateLogarithm InitialThetaWittLogarithmSeries
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem evaluation_coordinate (t : Tate D w) : evaluation D w (coordinate D w t) = 0 := by
  rw [coordinate, evaluation_ainfMap]
  have ht : InitialThetaTiltFontaine.theta D w (InitialThetaCyclotomicTateTilt.kernelCoordinate D w t) = 0 :=
    InitialThetaCyclotomicTateTilt.kernelCoordinate_mem_ker D w t
  exact congrArg Subtype.val ht

theorem evaluation_logTerm (t : Tate D w) (n : ℕ) :
    evaluation D w (logTerm D w (coordinate D w t) n) = 0 := by
  cases n with
  | zero => simp [logTerm, logCoefficient]
  | succ n =>
    rw [logTerm, Algebra.smul_def, map_mul, map_pow, evaluation_coordinate,
      zero_pow (Nat.succ_ne_zero n), mul_zero]

theorem evaluation_tateLog (t : Tate D w) : evaluation D w (tateLog D w t) = 0 := by
  have h : HasSum (fun n : ℕ => evaluation D w (logTerm D w (coordinate D w t) n))
      (evaluation D w (tateLog D w t)) :=
    (hasSum_tateLog D w t).map (evaluation D w) (evaluation_continuous D w)
  simp only [evaluation_logTerm] at h
  exact h.unique hasSum_zero

def teichLift (z : LocalGeometricFontaine.integerRing (Untilt D w)) :
    InitialThetaWittAllRadiusCompletion.Carrier D w :=
  InitialThetaWittAllRadiusExpansion.ainfMap D w (WittVector.teichmuller (Arithmetic.residueChar w.1)
    (InitialThetaTiltFontaine.integralLift D w z))

theorem evaluation_teichLift (z : LocalGeometricFontaine.integerRing (Untilt D w)) :
    evaluation D w (teichLift D w z) = (z : Untilt D w) := by
  rw [teichLift, evaluation_ainfMap]
  exact congrArg Subtype.val (InitialThetaTiltFontaine.theta_integralLift D w z)

theorem coordinateSeminorm_teichLift (ρ : InitialThetaWittRhoCompletion.Radius)
    (z : LocalGeometricFontaine.integerRing (Untilt D w)) :
    InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ (teichLift D w z) = ‖z‖ := by
  change ‖InitialThetaWittRhoExpansion.ainfMap D w ρ
    (WittVector.teichmuller (Arithmetic.residueChar w.1) (InitialThetaTiltFontaine.integralLift D w z))‖ = _
  rw [norm_ainf_teichmuller, InitialThetaTiltFontaine.integralLift_norm]

theorem evaluation_tateTranslate (z : LocalGeometricFontaine.integerRing (Untilt D w))
    (t : Tate D w) : evaluation D w (tateLog D w t + teichLift D w z) = (z : Untilt D w) := by
  rw [map_add, evaluation_tateLog, evaluation_teichLift, zero_add]

theorem tateTranslate_injective (z : LocalGeometricFontaine.integerRing (Untilt D w)) :
    Function.Injective (fun t : Tate D w => tateLog D w t + teichLift D w z) := by
  intro t s h
  exact InitialThetaWittTateLogarithmInjective.tateLog_injective D w (add_right_cancel h)

end
end JoshiTeich.Act1Scene1.InitialThetaWittThetaTateFiber
