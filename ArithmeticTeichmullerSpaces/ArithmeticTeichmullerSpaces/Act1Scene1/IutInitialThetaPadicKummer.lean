import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerPadicCohomology
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaKummerClass

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-KUMMER
source: Joshi III actual principal-unit class with Z_p(1) coefficients (3190--3208).
fidelity: constructs the standard continuous cohomology class over Z_p.
It uses the same actual cocycle and proves root-tower choice independence.
H^1_e membership and BK comparison remain open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer
open JoshiTeich.Prologue
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

local instance residuePrime (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩

def padicClass (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    continuousCohomology 1 (LocalKummer.padicTateTopRep (K := localField D s) (Ω := closure D s)
      (Arithmetic.residueChar s.1)) :=
  LocalKummer.toPadicH1 (Arithmetic.residueChar s.1) (kummerClass D s)

theorem padicClass_eq_representative
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    padicClass D s = LocalKummer.padicClassOfCocycle (Arithmetic.residueChar s.1)
      (continuousCocycleValue D s) := rfl

theorem padicClass_eq_of_rootTower
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (R : LocalKummer.RootTower (Ω := closure D s) (Arithmetic.residueChar s.1)
      (PaperLogWitnessHull.principalUnit D s)) :
    padicClass D s = LocalKummer.toPadicH1 (Arithmetic.residueChar s.1)
      (R.kummerClass (Arithmetic.residueChar_prime s.1).pos (principalUnit_ne_zero D s)) :=
  congrArg (LocalKummer.toPadicH1 (Arithmetic.residueChar s.1)) (kummerClass_eq_of_rootTower D s R)

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
