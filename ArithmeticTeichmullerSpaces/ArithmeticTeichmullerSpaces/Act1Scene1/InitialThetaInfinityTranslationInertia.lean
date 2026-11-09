import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityTranslationUnramified
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Flat.TorsionFree

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
Mathlib's actual Galois ramification and prime-inertia cardinality theorem.
fidelity: the original translation quotient acts on the original upper inverse
normalization over the original lower normalization. Its prime-inertia order
is the original ramification index, already proved to be one. No new group,
normalization, prime, algebra or valuation-inertia law is supplied by callers.
Original composition of existing project and Mathlib theorems.
boundary: this proves geometric translation inertia is trivial. The arithmetic
prime stabilizer can still act on the residue field; residue degree one,
projective cusps, AG.Cusp and theta-root identities are not asserted.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open FunctionFieldNormalization
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
  infinityTranslationBaseField_field infinityTranslationBaseField_rationalAlgebra
  infinityTranslationBaseField_baseAlgebra infinityTranslationBaseField_baseSMul
  infinityTranslationBaseField_baseModule infinityTranslationBaseField_coefficientAlgebra
  infinityTranslationBaseField_baseTower infinityTranslationBaseField_coefficientTower
  infinityTranslationBaseRing_baseAlgebra infinityTranslationBaseRing_baseSMul
  infinityTranslationBaseRing_baseModule infinityTranslationBaseRing_coefficientAlgebra
  infinityTranslationNormal
  infinityTranslationFieldAlgebra infinityTranslationFieldSMul infinityTranslationFieldModule
  infinityTranslationFieldAction infinityTranslationFieldActionSMul infinityTranslationFieldBaseComm
  infinityTranslationNormalizationAction infinityTranslationNormalizationSMul
  infinityTranslationRingAlgebra infinityTranslationRingSMul infinityTranslationRingModule
  infinityTranslationNormalizationGaloisGroup

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

local instance translationInertiaRing_finite :
    Module.Finite S.infinityTranslationBaseRing (S.infinityNormalizationRing false) :=
  moduleFinite_ringMap S.infinityTranslation_inverseCoordinate_transcendental
    S.infinityTranslationBaseField_le

local instance translationInertiaRing_integral :
    Algebra.IsIntegral S.infinityTranslationBaseRing (S.infinityNormalizationRing false) :=
  ⟨S.infinityTranslationRingMap_isIntegral⟩

local instance translationInertiaRing_torsionFree :
    Module.IsTorsionFree S.infinityTranslationBaseRing (S.infinityNormalizationRing false) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  exact S.infinityTranslationRingMap_injective

local instance translationInertiaRing_flat :
    Module.Flat S.infinityTranslationBaseRing (S.infinityNormalizationRing false) := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot]
  rw [← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

private theorem translationInertia_residueCharZero
    {k R : Type*} [Field k] [CharZero k] [CommRing R] [Algebra k R]
    (p : Ideal R) [p.IsPrime] : CharZero p.ResidueField := by
  let f : k →+* p.ResidueField :=
    (algebraMap R p.ResidueField).comp (algebraMap k R)
  exact charZero_of_injective_ringHom f.injective

local instance translationInertia_residueCharZeroAt
    (p : Ideal S.infinityTranslationBaseRing) [p.IsPrime] : CharZero p.ResidueField :=
  translationInertia_residueCharZero (k := ↥S.prime.torsionField) p

local instance translationInertia_residuePerfectAt
    (p : Ideal S.infinityTranslationBaseRing) [p.IsPrime] : PerfectField p.ResidueField :=
  PerfectField.ofCharZero

local instance translationInertia_separableResiduesAt
    (p : Ideal S.infinityTranslationBaseRing) [p.IsPrime] :
    Algebra.HasSeparableResidueFieldsAt S.infinityTranslationBaseRing
      (S.infinityNormalizationRing false) p := inferInstance

private theorem translationInertia_card_eq_ramificationIdx
    {R T G : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [IsDomain R] [IsDomain T] [Module.Finite R T] [Module.Flat R T]
    [Group G] [Finite G] [MulSemiringAction G T] [IsGaloisGroup G R T]
    (p : Ideal R) (P : Ideal T) [p.IsPrime] [P.IsPrime] [P.LiesOver p]
    [Algebra.HasSeparableResidueFieldsAt R T p] :
    Nat.card (P.inertia G) = P.ramificationIdx R :=
  (Ideal.card_inertia_eq_ramificationIdxIn (G := G) p P).trans
    (Ideal.ramificationIdxIn_eq_ramificationIdx p P G)

/-- The original translation inertia order is the original inverse-chart ramification index. -/
theorem infinityTranslationPrimeInertia_card_eq_ramificationIdx
    (q : S.infinityFiber false) :
    Nat.card (q.1.inertia S.infinityTranslationGroup) =
      q.1.ramificationIdx S.infinityTranslationBaseRing := by
  let p := (S.infinityTranslationFiberMap q).1
  letI : p.IsPrime := (S.infinityTranslationFiberMap q).2.1
  letI : q.1.IsPrime := q.2.1
  letI : q.1.LiesOver p := ⟨(S.infinityTranslationFiberMap_asIdeal q).symm⟩
  exact translationInertia_card_eq_ramificationIdx
    (G := S.infinityTranslationGroup) p q.1

/-- Consume the actual ramification-one theorem in the actual prime-inertia cardinality. -/
theorem infinityTranslationPrimeInertia_card_eq_one (q : S.infinityFiber false) :
    Nat.card (q.1.inertia S.infinityTranslationGroup) = 1 :=
  (S.infinityTranslationPrimeInertia_card_eq_ramificationIdx q).trans
    (S.infinityTranslation_ramificationIdx_one q)

/-- The original translation prime-inertia subgroup is trivial. -/
theorem infinityTranslationPrimeInertia_eq_bot (q : S.infinityFiber false) :
    q.1.inertia S.infinityTranslationGroup = ⊥ :=
  (q.1.inertia S.infinityTranslationGroup).eq_bot_iff_card.mpr
    (S.infinityTranslationPrimeInertia_card_eq_one q)

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
