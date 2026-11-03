import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittRhoActualValuePresentation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittRhoStandardValuePresentation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittRhoQuotientValue

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-RHO-QUOTIENT-COMPARISON
source: Joshi II `se:ff-rings`, weighted values on the original Away
presentations and the local-degree coefficient/contraction norm laws.
fidelity: exposes the proved quotient power comparison through the two
saved quotient functions and the original integral Witt map. No carrier,
norm, contraction or comparison hypothesis is changed.
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

local instance selectedPrimeQuotientComparison : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem choice_quotient_value_pow (ρ : ℝ≥0∞)
    (a : InitialThetaTiltFontaine.Ainf D w) (m : ℕ) :
    PadicWittRhoValue.awayQuotient (Arithmetic.residueChar w.1) ρ
        (InitialThetaPadicBoundedWittComparison.integerWittFun D w a) m ^
        Arithmetic.localDeg w.1 =
      actualChoiceQuotient D w (ρ ^ Arithmetic.localDeg w.1) a m :=
  quotient_value_pow D w ρ a m

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoComparison
