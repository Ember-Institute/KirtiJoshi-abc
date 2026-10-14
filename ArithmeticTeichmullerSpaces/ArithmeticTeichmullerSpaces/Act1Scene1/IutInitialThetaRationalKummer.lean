import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerRationalCohomology
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTateCoordinates

/-!
source-id: JT-SCENE1-INITIAL-THETA-RATIONAL-KUMMER
source: the actual principal-unit class with Q_p(1) coefficients, Joshi III (3214--3236).
fidelity: maps the actual integral cocycle to the usual p-adic coordinate
representation, identifies its coordinates and constructs its standard H1
class independently of root-tower choice. H^1_e/BK membership remains open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer
open JoshiTeich.Prologue
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

local instance rationalKummerResiduePrime
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩

local instance rationalKummerCharZero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

def rationalCocycle (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :=
  LocalKummer.Rational.cocycle (Arithmetic.residueChar s.1) (continuousCocycleValue D s)

theorem rationalCocycle_eq_coordinate
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (σ : closure D s ≃ₐ[localField D s] closure D s) :
    (rationalCocycle D s σ).down = (cocycleCoordinate D s σ : ℚ_[Arithmetic.residueChar s.1]) := rfl

def rationalClass (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    continuousCohomology 1 (LocalKummer.Rational.topRep (K := localField D s) (Ω := closure D s)
      (Arithmetic.residueChar s.1)) :=
  LocalKummer.Rational.toH1 (Arithmetic.residueChar s.1) (kummerClass D s)

theorem rationalClass_eq_representative
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    rationalClass D s = LocalKummer.Rational.classOfCocycle (Arithmetic.residueChar s.1)
      (continuousCocycleValue D s) := rfl

theorem rationalClass_eq_of_rootTower
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (R : LocalKummer.RootTower (Ω := closure D s) (Arithmetic.residueChar s.1)
      (PaperLogWitnessHull.principalUnit D s)) :
    rationalClass D s = LocalKummer.Rational.toH1 (Arithmetic.residueChar s.1)
      (R.kummerClass (Arithmetic.residueChar_prime s.1).pos (principalUnit_ne_zero D s)) :=
  congrArg (LocalKummer.Rational.toH1 (Arithmetic.residueChar s.1))
    (kummerClass_eq_of_rootTower D s R)

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
