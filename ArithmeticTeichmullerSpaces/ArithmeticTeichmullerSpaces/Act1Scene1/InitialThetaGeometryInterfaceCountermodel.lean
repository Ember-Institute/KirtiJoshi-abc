import ArithmeticTeichmullerSpaces.Act1Scene1.ProducerContracts

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: the explicit AnabelianGeometry, TemperedGeometry and geometry-seed
interfaces; IUT I Definition 3.1(d), the required cartesian covering square.
fidelity: an interface countermodel. Preserve every arithmetic, Tate and core
field of an existing seed, and every geometry operation except the unconstrained
cartesian predicate. Setting that predicate to False prevents OrbicurveData
and hence a universal geometry producer. This is not a claim about the actual
cartesian predicate of geometric orbicurves or about the cited mathematics.
boundary: Scene1/Derived. No positive producer or replacement geometry is asserted.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometryInterfaceCountermodel

open JoshiTeich.ReferenceIut
open JoshiTeich.ReferenceIut.OrbicurveDataSection
universe u
noncomputable section
variable (AG : AnabelianGeometry.{u}) (TG : TemperedGeometry AG)

def nonCartesianGeometry : AnabelianGeometry.{u} :=
  { AG with IsCartesianSquare := fun _ _ _ _ => False }

def nonCartesianTemperedGeometry : TemperedGeometry (nonCartesianGeometry AG) where
  tempPi1 := TG.tempPi1
  tempPi1Group := TG.tempPi1Group
  tempPi1Topology := TG.tempPi1Topology
  tempToEtale := TG.tempToEtale
  tempToEtale_continuous := TG.tempToEtale_continuous
  IsThetaRootModel := TG.IsThetaRootModel
  canonicalGraphCusp := TG.canonicalGraphCusp

def sameArithmeticSeed (S : InitialThetaGeometrySeed AG TG) :
    InitialThetaGeometrySeed (nonCartesianGeometry AG) (nonCartesianTemperedGeometry AG TG) where
  F := S.F
  fieldF := S.fieldF
  numberFieldF := S.numberFieldF
  Fbar := S.Fbar
  fieldFbar := S.fieldFbar
  algebraFbar := S.algebraFbar
  isAlgClosure := S.isAlgClosure
  E := S.E
  isElliptic := S.isElliptic
  VBad := S.VBad
  global := S.global
  prime := S.prime
  numberFieldK := S.numberFieldK
  algebraModK := S.algebraModK
  towerModK := S.towerModK
  tate := S.tate
  core := S.core

theorem no_orbicurveData (S : InitialThetaGeometrySeed AG TG) :
    ¬ Nonempty (OrbicurveData (nonCartesianGeometry AG) S.F S.E S.Fbar S.VBad S.prime) := by
  rintro ⟨O⟩
  exact O.diagram_cartesian

theorem no_producer (S : InitialThetaGeometrySeed AG TG) :
    ¬ Nonempty (InitialThetaGeometryProducer
      (nonCartesianGeometry AG) (nonCartesianTemperedGeometry AG TG)) := by
  rintro ⟨P⟩
  exact no_orbicurveData AG TG S ⟨(P.produce (sameArithmeticSeed AG TG S)).choose⟩

theorem no_universal_producer (S : InitialThetaGeometrySeed AG TG) :
    ¬ (∀ (A : AnabelianGeometry.{u}) (T : TemperedGeometry A),
      Nonempty (InitialThetaGeometryProducer A T)) := by
  intro h
  exact no_producer AG TG S (h (nonCartesianGeometry AG) (nonCartesianTemperedGeometry AG TG))

end
end JoshiTeich.Act1Scene1.InitialThetaGeometryInterfaceCountermodel
