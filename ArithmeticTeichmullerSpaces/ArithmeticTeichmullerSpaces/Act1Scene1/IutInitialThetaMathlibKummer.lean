import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerMathlibCohomology
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaKummerClass

/-!
source-id: JT-SCENE1-INITIAL-THETA-MATHLIB-KUMMER
source: Joshi III actual principal-unit Kummer class (3190--3208).
fidelity: constructs the class in Mathlib continuous cohomology of the local
Galois group with the additive inverse-limit Tate coefficients. Its explicit
homogeneous representative is the actual Kummer cocycle. Root choice does
not change this standard class. H^1_e and BK comparison remain open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer
open JoshiTeich.Prologue
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

def mathlibClass (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    continuousCohomology 1 (LocalKummer.tateTopRep (K := localField D s) (Ω := closure D s)
      (Arithmetic.residueChar s.1)) :=
  LocalKummer.toMathlibH1 (kummerClass D s)

theorem mathlibClass_eq_representative
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    mathlibClass D s = LocalKummer.mathlibClassOfCocycle (continuousCocycleValue D s) := rfl

theorem mathlibClass_eq_of_rootTower
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (R : LocalKummer.RootTower (Ω := closure D s) (Arithmetic.residueChar s.1)
      (PaperLogWitnessHull.principalUnit D s)) :
    mathlibClass D s = LocalKummer.toMathlibH1
      (R.kummerClass (Arithmetic.residueChar_prime s.1).pos (principalUnit_ne_zero D s)) :=
  congrArg LocalKummer.toMathlibH1 (kummerClass_eq_of_rootTower D s R)

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
