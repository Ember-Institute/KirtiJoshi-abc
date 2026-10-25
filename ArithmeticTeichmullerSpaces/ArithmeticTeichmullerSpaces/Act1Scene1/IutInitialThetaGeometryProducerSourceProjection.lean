import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaGeometryReferenceExistenceAdapter
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaLinkSource

namespace JoshiTeich.Act1Scene1

open JoshiTeich.ReferenceIut
open JoshiTeich.Prologue

universe u

noncomputable section

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-!
source-id: JT-SCENE1-INITIAL-THETA-GEOMETRY-PRODUCER-SOURCE-PROJECTION
source: the reference `thetaData` assembly in
`refer/iut/Iut/Concrete/Existence.lean`, the Scene1 producer contract, and
the canonical actual Tate source in `IutInitialThetaLinkSource.lean`.
fidelity: proves that a producer's assembled InitialThetaData retains the
seed's arithmetic, admissible-prime, and Tate-family fields, and that the
same output immediately supplies the canonical finite Tate-parameter laws.
boundary: this is a projection and consumer theorem. It does not produce an
inhabitant of the geometric producer or prove the missing orbicurve/local
existence witness.
-/

namespace InitialThetaGeometryProducer

variable (P : InitialThetaGeometryProducer AG TG)
variable (S : InitialThetaGeometrySeed AG TG)

theorem toInitialThetaData_F :
    (P.toInitialThetaData S).F = S.F := rfl

theorem toInitialThetaData_Fbar :
    (P.toInitialThetaData S).Fbar = S.Fbar := rfl

theorem toInitialThetaData_E :
    (P.toInitialThetaData S).E = S.E := rfl

theorem toInitialThetaData_VBad :
    (P.toInitialThetaData S).VBad = S.VBad := rfl

theorem toInitialThetaData_global :
    (P.toInitialThetaData S).global = S.global := rfl

theorem toInitialThetaData_prime :
    (P.toInitialThetaData S).prime = S.prime := rfl

theorem toInitialThetaData_tate :
    (P.toInitialThetaData S).tate = S.tate := rfl

theorem toInitialThetaData_tateParameterData_laws :
    Theta.TateParameterLaws
      (iutInitialThetaTateParameterData (P.toInitialThetaData S)) :=
  iutInitialThetaTateParameterData_laws (P.toInitialThetaData S)

end InitialThetaGeometryProducer

end
end JoshiTeich.Act1Scene1
