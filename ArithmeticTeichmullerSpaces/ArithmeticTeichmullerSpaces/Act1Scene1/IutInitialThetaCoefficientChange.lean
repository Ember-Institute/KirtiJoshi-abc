import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerCoefficientChange
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRationalKummer

/-!
source-id: JT-SCENE1-INITIAL-THETA-COEFFICIENT-CHANGE
source: Joshi III (3214--3236), rationalization of the actual integral Kummer class.
fidelity: the actual standard rational class is the coefficient change of the
actual standard integral class. No H1 injectivity or H^1_e identity is assumed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer
open JoshiTeich.Prologue
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

local instance coefficientChangeResiduePrime
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩

local instance coefficientChangeCharZero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

theorem rationalClass_eq_changeCoefficients
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    rationalClass D s = LocalKummer.Rational.standardMap (Arithmetic.residueChar s.1) (padicClass D s) :=
  (LocalKummer.Rational.standardMap_toPadicH1 (Arithmetic.residueChar s.1) (kummerClass D s)).symm

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
