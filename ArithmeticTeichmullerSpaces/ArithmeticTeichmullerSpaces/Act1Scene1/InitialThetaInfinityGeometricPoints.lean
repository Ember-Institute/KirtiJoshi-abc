import Lean.LibrarySuggestions.Basic
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityRamification
import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricPointInertia

/-!
source-id: JT-SCENE1-INITIAL-THETA-INFINITY-GEOMETRIC-POINTS-20261107
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
Mathlib's residue-field geometric points and inertia stabilizers.
fidelity: constructs the residue-closure point of each actual inverse-chart
infinity prime. Its kernel is that prime, the geometric stabilizer is its
actual inertia subgroup, and restriction to the signed chart has the original
infinityFiberMap as its kernel.
boundary: this does not identify the boundary point with elliptic torsion,
the distinguished cusp, epsilon, or an arbitrary orbicurve cusp.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] inverseCoordinateRationalBase_coefficientAlgebra
  inverseCoordinateRationalBase_coefficientSMul inverseCoordinateRationalBase_coefficientModule
  inverseCoordinatePolynomialBaseRationalBaseAlgebra inverseCoordinatePolynomialBaseRationalBaseSMul
  inverseCoordinatePolynomialBaseRationalBaseModule inverseCoordinatePolynomialBaseRationalBaseTower
  infinityNormalizationField_field infinityNormalizationField_rationalBaseAlgebra
  infinityNormalizationField_baseAlgebra infinityNormalizationField_baseSMul
  infinityNormalizationField_baseModule infinityNormalizationField_coefficientAlgebra
  infinityNormalizationField_coefficientSMul infinityNormalizationField_coefficientModule
  infinityNormalizationField_coefficientBaseTower infinityNormalizationField_baseTower
  infinityNormalizationRing_baseAlgebra infinityNormalizationRing_baseSMul
  infinityNormalizationRing_baseModule infinityNormalizationRing_coefficientAlgebra
  infinityNormalizationRing_isDedekindDomain infinityNormalizationRing_finite
  infinityNormalizationRing_fractionField
  infinitySignedFieldAlgebra infinitySignedFieldSMul infinitySignedFieldModule
  infinitySignedFieldBaseTower infinitySignedFieldAction infinitySignedFieldActionSMul
  infinityFieldBaseComm infinitySignedNormalizationAction infinitySignedNormalizationActionSMul
  infinitySignedRingAlgebra infinitySignedRingSMul infinitySignedRingModule
  infinitySignedNormalizationGaloisGroup

attribute [local instance] infinitySignedNormalizationAction

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

local instance infinityNormalizationPointAction (C : Type u) [CommRing C] :
    MulAction S.signedCoverQuotientGroup
      (S.infinityNormalizationRing false →+* C) :=
  GeometricPointInertia.pointAction S.signedCoverQuotientGroup
    (S.infinityNormalizationRing false) C

attribute [local instance] infinityNormalizationPointAction

/-- The actual residue-closure geometric point above an infinity prime. -/
def infinityNormalizationGeometricPoint (q : S.infinityFiber false) :
    S.infinityNormalizationRing false →+* AlgebraicClosure q.1.ResidueField :=
  by
    letI : q.1.IsPrime := q.2.1
    exact GeometricPointInertia.residueGeometricPoint q.1

theorem infinityNormalizationGeometricPoint_ker (q : S.infinityFiber false) :
    RingHom.ker (S.infinityNormalizationGeometricPoint q) = q.1 := by
  letI : q.1.IsPrime := q.2.1
  exact GeometricPointInertia.ker_residueGeometricPoint q.1

/-- The geometric stabilizer of the actual infinity point is its inertia subgroup. -/
theorem infinityNormalizationGeometricPoint_stabilizer (q : S.infinityFiber false) :
    MulAction.stabilizer S.signedCoverQuotientGroup
      (S.infinityNormalizationGeometricPoint q) =
        q.1.inertia S.signedCoverQuotientGroup := by
  letI : q.1.IsPrime := q.2.1
  exact (GeometricPointInertia.stabilizer_eq_inertia
    S.signedCoverQuotientGroup (S.infinityNormalizationRing false)
    (AlgebraicClosure q.1.ResidueField) (S.infinityNormalizationGeometricPoint q)).trans
      (congrArg (fun I : Ideal (S.infinityNormalizationRing false) =>
        I.inertia S.signedCoverQuotientGroup) (S.infinityNormalizationGeometricPoint_ker q))

set_option maxHeartbeats 1000000 in
theorem infinityNormalizationGeometricPoint_stabilizer_card (q : S.infinityFiber false) :
    Nat.card (MulAction.stabilizer S.signedCoverQuotientGroup
      (S.infinityNormalizationGeometricPoint q)) =
        Nat.card (q.1.inertia S.signedCoverQuotientGroup) := by
  exact congrArg (fun H : Subgroup S.signedCoverQuotientGroup => Nat.card H)
    (S.infinityNormalizationGeometricPoint_stabilizer q)

set_option maxHeartbeats 1000000 in
/-- Restriction of the geometric point to the signed chart has the actual signed center. -/
theorem infinityNormalizationGeometricPoint_signedKernel (q : S.infinityFiber false) :
    RingHom.ker
      ((S.infinityNormalizationGeometricPoint q).comp
        S.infinityNormalizationRingMap.toRingHom) = (S.infinityFiberMap q).1 := by
  calc
    RingHom.ker ((S.infinityNormalizationGeometricPoint q).comp
        S.infinityNormalizationRingMap.toRingHom) =
      (RingHom.ker (S.infinityNormalizationGeometricPoint q)).comap
        S.infinityNormalizationRingMap.toRingHom :=
      (RingHom.comap_ker (S.infinityNormalizationGeometricPoint q)
        S.infinityNormalizationRingMap.toRingHom).symm
    _ = q.1.comap S.infinityNormalizationRingMap.toRingHom :=
      congrArg (fun I : Ideal (S.infinityNormalizationRing false) =>
        I.comap S.infinityNormalizationRingMap.toRingHom)
        (S.infinityNormalizationGeometricPoint_ker q)
    _ = (S.infinityFiberMap q).1 := (S.infinityFiberMap_asIdeal q).symm

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

/- Lean 4.33.1's symbol-frequency exporter stalls on these dependent wrapper
   types. Skip their suggestion index while retaining every declaration and proof. -/
open Lean in
run_cmd do
  for name in ["infinityNormalizationGeometricPoint_ker", "infinityNormalizationGeometricPoint_stabilizer", "infinityNormalizationGeometricPoint_stabilizer_card", "infinityNormalizationGeometricPoint_signedKernel"] do
    modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env name
