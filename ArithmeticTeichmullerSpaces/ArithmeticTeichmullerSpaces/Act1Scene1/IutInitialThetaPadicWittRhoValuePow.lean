import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittRhoValueTransfer

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-RHO-VALUE-POW
source: Joshi II `se:ff-rings`, weighted Teichmuller values on the bounded
Witt localization, and the actual-to-standard tilt comparison.
fidelity: specializes the whole presentation comparison function to the
original actual/standard bounded-ring equivalence. The numerator and
contraction denominator laws are proved separately from the original
coefficient norms and local degree. This is an algebraic value comparison;
it does not identify a Frechet completion or the paper's B.
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

local instance selectedPrimeValuePow : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem value_pow
    (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤)
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    PadicWittRhoValue.value (Arithmetic.residueChar w.1) ρ
        (InitialThetaPadicBoundedWittComparison.ringEquiv D w x) ^
        Arithmetic.localDeg w.1 =
      InitialThetaWittRhoValue.value D w (ρ ^ Arithmetic.localDeg w.1) x :=
  value_pow_function D w ρ hρ0 hρtop x

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoComparison
