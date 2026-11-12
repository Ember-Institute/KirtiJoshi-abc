import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityOrbit
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityFiber
import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationRamification
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Flat.TorsionFree

/-!
source-id: JT-SCENE1-INITIAL-THETA-INFINITY-RAMIFICATION-20261107
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
Mathlib's Galois ramification and inertia cardinality comparisons.
fidelity: transports the actual signed/unsigned ramification laws to the
inverse-coordinate normalization at the closed boundary fibers. The inertia
cardinality and arithmetic stabilizer formulas use the actual signed quotient
action and the actual `k[(xG)⁻¹]` integral closures.
boundary: this supplies boundary multiplicity laws. It does not identify the
boundary with torsion cusps, geometric points, epsilon, or an orbicurve model.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical Pointwise IntermediateField.algebraAdjoinAdjoin
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

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

private abbrev ramificationCoefficientField := ↥S.prime.torsionField
private abbrev ramificationInverseCoordinate := (Genuine.xG S.prime.EK)⁻¹

private theorem infinityNormalizationField_signed_le_unsigned :
    S.infinityNormalizationField true ≤ S.infinityNormalizationField false :=
  by
    intro x hx
    have hx' := (S.mem_infinityNormalizationField true x).mp hx
    exact (S.mem_infinityNormalizationField false x).mpr
      (Genuine.normalizationField_signed_le_unsigned S.prime.EK S.prime.ℓ S.prime.M hx')

private theorem inverseCoordinate_transcendental :
    Transcendental (ramificationCoefficientField S) (ramificationInverseCoordinate S) := by
  intro h
  exact Genuine.transcendental_xG S.prime.EK
    ((IsAlgebraic.inv_iff (R := ramificationCoefficientField S)
      (x := Genuine.xG S.prime.EK)).mp (by simpa using h))

local instance infinityRamificationRingAlgebra :
    Algebra (S.infinityNormalizationRing true) (S.infinityNormalizationRing false) :=
  S.infinitySignedRingAlgebra

local instance infinityRamificationRingSMul :
    SMul (S.infinityNormalizationRing true) (S.infinityNormalizationRing false) :=
  S.infinitySignedRingAlgebra.toSMul

local instance infinityRamificationRingModule :
    Module (S.infinityNormalizationRing true) (S.infinityNormalizationRing false) :=
  S.infinitySignedRingAlgebra.toModule

local instance infinityRamificationRingFinite :
    Module.Finite (S.infinityNormalizationRing true) (S.infinityNormalizationRing false) := by
  exact FunctionFieldNormalization.moduleFinite_ringMap
    (inverseCoordinate_transcendental S)
    S.infinityNormalizationField_signed_le_unsigned

local instance infinityRamificationRingIntegral :
    Algebra.IsIntegral (S.infinityNormalizationRing true) (S.infinityNormalizationRing false) :=
  ⟨FunctionFieldNormalization.ringMap_isIntegral S.infinityNormalizationField_signed_le_unsigned⟩

local instance infinityRamificationRingTorsionFree :
    Module.IsTorsionFree (S.infinityNormalizationRing true)
      (S.infinityNormalizationRing false) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  exact FunctionFieldNormalization.ringMap_injective
    S.infinityNormalizationField_signed_le_unsigned

local instance infinityRamificationRingFlat :
    Module.Flat (S.infinityNormalizationRing true) (S.infinityNormalizationRing false) :=
  by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot]
    rw [← Submodule.isTorsionFree_iff_torsion_eq_bot]
    infer_instance

local instance infinityRamificationRingIdealAction :
    MulAction S.signedCoverQuotientGroup
      (Ideal (S.infinityNormalizationRing false)) :=
  (Ideal.pointwiseDistribMulAction (M := S.signedCoverQuotientGroup)
    (R := S.infinityNormalizationRing false)).toMulAction

local instance infinityRamificationRingGaloisGroup :
    IsGaloisGroup S.signedCoverQuotientGroup
      (S.infinityNormalizationRing true) (S.infinityNormalizationRing false) :=
  S.infinitySignedNormalizationGaloisGroup

private def infinitySignedRamificationMultiplicity
    (p : Ideal (S.infinityNormalizationRing true)) : ℕ :=
  letI := S.infinitySignedRingAlgebra
  p.ramificationIdxIn (S.infinityNormalizationRing false)

private theorem infinitySignedRamificationMultiplicity_eq_ramificationIdx
    (p : Ideal (S.infinityNormalizationRing true)) [p.IsPrime]
    (P : Ideal (S.infinityNormalizationRing false)) [P.IsPrime] [P.LiesOver p] :
    infinitySignedRamificationMultiplicity S p =
        P.ramificationIdx (S.infinityNormalizationRing true) :=
  Ideal.ramificationIdxIn_eq_ramificationIdx p P S.signedCoverQuotientGroup

private theorem infinityResidueCharZero
    {K R : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R]
    (p : Ideal R) [p.IsPrime] : CharZero p.ResidueField := by
  let f : K →+* p.ResidueField :=
    (algebraMap R p.ResidueField).comp (algebraMap K R)
  exact charZero_of_injective_ringHom f.injective

local instance infinityResidueCharZeroAt
    (p : Ideal (S.infinityNormalizationRing true)) [p.IsPrime] :
    CharZero p.ResidueField :=
  infinityResidueCharZero (K := S.prime.torsionField) p

local instance infinityResiduePerfectAt
    (p : Ideal (S.infinityNormalizationRing true)) [p.IsPrime] :
    PerfectField p.ResidueField := PerfectField.ofCharZero

set_option maxHeartbeats 1000000 in
/-- The inverse-coordinate infinity multiplicity equals the actual inertia order. -/
theorem infinitySignedRamificationMultiplicity_eq_card_inertia
    (q : S.infinityFiber false) :
    infinitySignedRamificationMultiplicity S (S.infinityFiberMap q).1 =
      Nat.card (q.1.inertia S.signedCoverQuotientGroup) := by
  let p := (S.infinityFiberMap q).1
  letI : p.IsPrime := (S.infinityFiberMap q).2.1
  letI : q.1.IsPrime := q.2.1
  letI : q.1.LiesOver p := by
    exact ⟨(S.infinityFiberMap_asIdeal q).symm⟩
  calc
    infinitySignedRamificationMultiplicity S p =
        q.1.ramificationIdx (S.infinityNormalizationRing true) :=
      S.infinitySignedRamificationMultiplicity_eq_ramificationIdx p q.1
    _ = p.ramificationIdxIn (S.infinityNormalizationRing false) :=
      (Ideal.ramificationIdxIn_eq_ramificationIdx p q.1
        S.signedCoverQuotientGroup).symm
    _ = Nat.card (q.1.inertia S.signedCoverQuotientGroup) :=
      (Ideal.card_inertia_eq_ramificationIdxIn
        (G := S.signedCoverQuotientGroup) p q.1).symm

/-- The arithmetic stabilizer order retains the residue-degree factor. -/
theorem infinitySignedNormalization_card_stabilizer
    (q : S.infinityFiber false) :
    Nat.card (MulAction.stabilizer S.signedCoverQuotientGroup q.1) =
      infinitySignedRamificationMultiplicity S (S.infinityFiberMap q).1 *
        (S.infinityFiberMap q).1.inertiaDegIn (S.infinityNormalizationRing false) := by
  let p := (S.infinityFiberMap q).1
  letI : p.IsPrime := (S.infinityFiberMap q).2.1
  letI : q.1.IsPrime := q.2.1
  letI : q.1.LiesOver p := by
    exact ⟨(S.infinityFiberMap_asIdeal q).symm⟩
  exact Ideal.card_stabilizer_eq (G := S.signedCoverQuotientGroup) p q.1

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
