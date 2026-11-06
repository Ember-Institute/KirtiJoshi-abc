import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittFrobeniusNumerator
import ArithmeticTeichmullerSpaces.Act1Scene1.WittFrobeniusPresentation

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-FROBENIUS-NATIVE-NUMERATOR
source: Joshi II `se:ff-rings`, Frobenius on denominator-power numerator
presentations and the original coefficient comparison.
fidelity: states the proved numerator naturality with both native Ainf
carriers and the original integerWittFun. The correction factor and the
original Witt Frobenius are retained. No comparison law is added.
Original proof; no reference implementation copied. Prologue R5 unchanged.
boundary: numerator comparison only; bounded, completion and paper
identifications are separate obligations.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicWittFrobeniusPresentationTransfer

open JoshiTeich.Prologue
open InitialThetaPadicBoundedWittComparison
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeNativeFrobeniusNumerator :
    Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem integerWittFun_transform (m : ℕ) (a : InitialThetaTiltFontaine.Ainf D w) :
    integerWittFun D w
        (WittFrobeniusPresentation.transform (Arithmetic.residueChar w.1) m a) =
      WittFrobeniusPresentation.transform (Arithmetic.residueChar w.1) m
        (integerWittFun D w a) :=
  integerNumeratorNaturality D w m a

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittFrobeniusPresentationTransfer
