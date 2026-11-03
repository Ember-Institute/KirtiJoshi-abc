import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicBoundedWittComparison

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-RHO-DENOMINATOR-POWER
source: Joshi II `se:ff-rings`, the contraction denominator and the proved
local-degree norm law on the actual and independent standard tilt integers.
fidelity: states the proved radius power formula with the original named
contractions, their original norms, and the local degree.
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

local instance selectedPrimeDenominatorPower : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem denominator_value_pow (ρ : ℝ≥0∞) :
    (ρ * ENNReal.ofReal
        ‖PadicBoundedWittLocalization.contraction (Arithmetic.residueChar w.1)‖) ^
        Arithmetic.localDeg w.1 =
      ρ ^ Arithmetic.localDeg w.1 *
        ENNReal.ofReal ‖InitialThetaPadicBoundedWittComparison.contraction D w‖ :=
  InitialThetaPadicBoundedWittComparison.contraction_radius_pow D w ρ

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoComparison
