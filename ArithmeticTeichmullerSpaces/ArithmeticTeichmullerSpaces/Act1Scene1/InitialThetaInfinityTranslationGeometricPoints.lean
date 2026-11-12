import Lean.LibrarySuggestions.Basic
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityGeometricPoints
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityTranslationGalois
import ArithmeticTeichmullerSpaces.Act1Scene1.OrbitStabilizerNatCard

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`.
fidelity: the original translation quotient acts on the original residue geometric
point; its stabilizer is the original prime inertia, and orbit size times inertia
order is the same admissible prime ell. Consumes the actual TK/M group identity.
Original proofs; no reference implementation copied.
boundary: this does not prove inertia or prime stabilizers trivial, residue degree
one, a torsion-boundary equivalence, projective cusps, AG.Cusp or theta-root data.
-/

namespace JoshiTeich.Act1Scene1

private theorem translationOrbit_card_mul_of_stabilizer_card
    {G X : Type*} [Group G] [MulAction G X]
    (x : X) {i n : ℕ}
    (hi : Nat.card (MulAction.stabilizer G x) = i)
    (hn : Nat.card G = n) :
    Nat.card (MulAction.orbit G x) * i = n :=
  (congrArg (fun m : ℕ => Nat.card (MulAction.orbit G x) * m) hi.symm).trans
    ((OrbitStabilizerNatCard.orbit_card_mul_stabilizer_card x).trans hn)

end JoshiTeich.Act1Scene1

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

attribute [local instance] infinityTranslationNormal
  infinityTranslationFieldAlgebra infinityTranslationFieldSMul infinityTranslationFieldModule
  infinityTranslationFieldAction infinityTranslationFieldActionSMul
  infinityTranslationFieldBaseComm infinityTranslationNormalizationAction
  infinityTranslationNormalizationSMul

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

local instance infinityTranslationGeometricPointAction (C : Type u) [CommRing C] :
    MulAction S.infinityTranslationGroup
      (S.infinityNormalizationRing false →+* C) :=
  GeometricPointInertia.pointAction S.infinityTranslationGroup
    (S.infinityNormalizationRing false) C

/-- The original translation stabilizer of the actual residue point is its inertia. -/
theorem infinityTranslationGeometricPoint_stabilizer (q : S.infinityFiber false) :
    MulAction.stabilizer S.infinityTranslationGroup
      (S.infinityNormalizationGeometricPoint q) =
      q.1.inertia S.infinityTranslationGroup := by
  letI : q.1.IsPrime := q.2.1
  exact (GeometricPointInertia.stabilizer_eq_inertia
    S.infinityTranslationGroup (S.infinityNormalizationRing false)
    (AlgebraicClosure q.1.ResidueField) (S.infinityNormalizationGeometricPoint q)).trans
      (congrArg (fun I : Ideal (S.infinityNormalizationRing false) =>
        I.inertia S.infinityTranslationGroup) (S.infinityNormalizationGeometricPoint_ker q))

theorem infinityTranslationGeometricPoint_stabilizer_card (q : S.infinityFiber false) :
    Nat.card (MulAction.stabilizer S.infinityTranslationGroup
      (S.infinityNormalizationGeometricPoint q)) =
      Nat.card (q.1.inertia S.infinityTranslationGroup) :=
  congrArg (fun H : Subgroup S.infinityTranslationGroup => Nat.card H)
    (S.infinityTranslationGeometricPoint_stabilizer q)

/-- The original translation quotient has order the original admissible prime. -/
theorem infinityTranslationGroup_card_eq_ell :
    Nat.card S.infinityTranslationGroup = S.prime.ℓ :=
  (Nat.card_congr S.functionFieldCoverTranslationQuotientEquiv.toEquiv).trans
    ((Nat.card_congr Multiplicative.toAdd).trans S.prime.card_rankOneQuotient)

/-- Consume both actual identities in the original geometric orbit formula. -/
theorem infinityTranslationGeometricOrbit_mul_inertia_card
    (q : S.infinityFiber false) :
    Nat.card (MulAction.orbit S.infinityTranslationGroup
      (S.infinityNormalizationGeometricPoint q)) *
      Nat.card (q.1.inertia S.infinityTranslationGroup) = S.prime.ℓ :=
  translationOrbit_card_mul_of_stabilizer_card
    (S.infinityNormalizationGeometricPoint q)
    (S.infinityTranslationGeometricPoint_stabilizer_card q)
    S.infinityTranslationGroup_card_eq_ell

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

/- Lean 4.33.1's symbol-frequency exporter stalls on these dependent wrapper
   types. Skip their suggestion index while retaining every declaration and proof. -/
open Lean in
run_cmd do
  for name in ["infinityTranslationGeometricPoint_stabilizer", "infinityTranslationGeometricPoint_stabilizer_card", "infinityTranslationGroup_card_eq_ell", "infinityTranslationGeometricOrbit_mul_inertia_card"] do
    modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env name
