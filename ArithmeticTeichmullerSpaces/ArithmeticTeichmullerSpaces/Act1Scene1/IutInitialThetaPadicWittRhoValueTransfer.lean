import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittRhoValueInterface
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittRhoActualValuePresentation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittRhoStandardValuePresentation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittRhoQuotientComparison

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-RHO-VALUE-TRANSFER
source: Joshi II `se:ff-rings`, the two localization presentation formulas
and the original local-degree coefficient norm power law.
fidelity: specializes the abstract presentation comparison to the existing
choice equivalence, independent standard localization, and original value
functions. The quotient law is proved by the coefficient and contraction
norm laws. No new comparison hypothesis or completed-ring identity is used.
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

local instance selectedPrimeValueTransfer : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem value_pow_function :
    ∀ (ρ : ℝ≥0∞), ρ ≠ 0 → ρ ≠ ⊤ →
      ∀ x : InitialThetaBoundedWittLocalization.Ring D w,
        PadicWittRhoValue.value (Arithmetic.residueChar w.1) ρ
            (InitialThetaPadicBoundedWittComparison.ringEquiv D w x) ^
            Arithmetic.localDeg w.1 =
          InitialThetaWittRhoValue.value D w (ρ ^ Arithmetic.localDeg w.1) x :=
  presentation_value_transfer D w
    (actual_choice_value_presentation D w)
    (standard_choice_value_presentation D w)
    (choice_quotient_value_pow D w)

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoComparison
