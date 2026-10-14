import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerCohomology
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaContinuousKummer

/-!
source-id: JT-SCENE1-INITIAL-THETA-KUMMER-CLASS
source: Joshi III principal-unit compatible roots and Kummer class (3190--3208).
fidelity: constructs the continuous cohomology class of the actual p*-principal
unit at each full-support torsion place. Any compatible root tower of that
unit gives the same class. H^1_e membership and BK comparison remain open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer
open JoshiTeich.Prologue
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

def continuousCocycleValue (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalKummer.continuousCocycles (K := localField D s) (Ω := closure D s)
      (Arithmetic.residueChar s.1) :=
  ⟨continuousCocycle D s, continuousCocycle_isMulCocycle D s⟩

def kummerClass (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalKummer.continuousH1 (K := localField D s) (Ω := closure D s)
      (Arithmetic.residueChar s.1) :=
  LocalKummer.continuousH1Class (continuousCocycleValue D s)

theorem kummerClass_eq_of_rootTower
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (R : LocalKummer.RootTower (Ω := closure D s) (Arithmetic.residueChar s.1)
      (PaperLogWitnessHull.principalUnit D s)) :
    kummerClass D s =
      R.kummerClass (Arithmetic.residueChar_prime s.1).pos (principalUnit_ne_zero D s) :=
  (rootTower D s).kummerClass_eq R _ _

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
