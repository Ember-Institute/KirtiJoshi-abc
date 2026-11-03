import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittRhoValuePow
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoNorm
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittRhoNorm

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-RHO-REAL-VALUE
source: Joshi II `se:ff-rings`, the original weighted rho values under the
proved actual-to-standard tilt norm comparison.
fidelity: applies toReal to the existing value power identity. Both real
values remain the toReal of their original ENNReal values; the standard
radius rho corresponds to actual radius rho^localDeg. No norm is replaced.
Original proof; Scene1/Derived; Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoComparison

open JoshiTeich.Prologue
open scoped ENNReal
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeRealValue : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem realValue_pow (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤)
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    PadicWittRhoNorm.realValue (Arithmetic.residueChar w.1) ρ
        (InitialThetaPadicBoundedWittComparison.ringEquiv D w x) ^
        Arithmetic.localDeg w.1 =
      InitialThetaWittRhoNorm.realValue D w (ρ ^ Arithmetic.localDeg w.1) x := by
  simpa only [PadicWittRhoNorm.realValue, InitialThetaWittRhoNorm.realValue,
    ENNReal.toReal_pow] using congrArg ENNReal.toReal (value_pow D w ρ hρ0 hρtop x)

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoComparison
