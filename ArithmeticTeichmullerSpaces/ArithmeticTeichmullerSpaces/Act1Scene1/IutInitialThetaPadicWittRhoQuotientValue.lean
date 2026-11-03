import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittRhoNumerator
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittRhoDenominatorPower
import ArithmeticTeichmullerSpaces.Act1Scene1.WittRhoPresentation

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-RHO-QUOTIENT-VALUE
source: Joshi II `se:ff-rings`, weighted Witt numerator values and the
contraction denominator under the local-degree power law.
fidelity: combines the proved numerator and denominator power formulas
through the scalar quotient identity for the original named values.
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

local instance selectedPrimeQuotientValue : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

set_option linter.defProp false in
def quotient_value_pow (ρ : ℝ≥0∞) (a : InitialThetaTiltFontaine.Ainf D w) (m : ℕ) :=
  WittRhoPresentation.quotient_pow_of_power _ _ _ _ (Arithmetic.localDeg w.1) m
    (numerator_value_pow D w a ρ) (denominator_value_pow D w ρ)

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoComparison
