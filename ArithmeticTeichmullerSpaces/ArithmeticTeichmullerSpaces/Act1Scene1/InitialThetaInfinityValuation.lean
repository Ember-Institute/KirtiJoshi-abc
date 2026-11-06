import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityFiber
import ArithmeticTeichmullerSpaces.Act1Scene1.NormalizationPrimeValuationExtension

/-!
source-id: JT-SCENE1-INITIAL-THETA-INFINITY-AMBIENT-VALUATION-20261107
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
the valuation description of the punctures in Genuine/Pi1.lean.
fidelity: constructs an ambient valuation ring over every actual infinity
prime, with that prime as its exact center. It contains the constant field,
and the original x-coordinate has a pole. The same ambient valuation has the
expected signed center under the original signed field inclusion.
Original proofs; no reference implementation copied.
boundary: this supplies actual boundary valuations and their centers. The
torsion-cusp equivalence, distinguished epsilon, theta-root model and the
geometry producer remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section

private theorem valuation_center_comap {A B Ω : Type*}
    [CommRing A] [CommRing B] [Field Ω]
    (W : ValuationSubring Ω) (i : A →+* B) (fA : A →+* Ω) (fB : B →+* Ω)
    (hmap : ∀ a, fB (i a) = fA a) (Q : Ideal B) (P : Ideal A)
    (hP : P = Q.comap i)
    (hcenter : ∀ b, W.valuation (fB b) < 1 ↔ b ∈ Q) (a : A) :
    W.valuation (fA a) < 1 ↔ a ∈ P := by
  rw [hP, Ideal.mem_comap, ← hmap a]
  exact hcenter (i a)

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

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

/-- The original ambient embedding of the inverse-coordinate normalization ring. -/
def infinityNormalizationAmbientMap (pm : Bool) :
    S.infinityNormalizationRing pm →+* Genuine.Ω S.prime.EK :=
  (S.infinityNormalizationField pm).val.toRingHom.comp
    (algebraMap (S.infinityNormalizationRing pm) (S.infinityNormalizationField pm))

theorem infinityNormalizationAmbientMap_apply (pm : Bool)
    (a : S.infinityNormalizationRing pm) :
    S.infinityNormalizationAmbientMap pm a =
      ((a : S.infinityNormalizationField pm) : Genuine.Ω S.prime.EK) := rfl

private theorem infinityAmbientValuation_exists (pm : Bool) (q : S.infinityFiber pm) :
    ∃ W : ValuationSubring (Genuine.Ω S.prime.EK),
      (∀ a : S.infinityNormalizationRing pm, S.infinityNormalizationAmbientMap pm a ∈ W) ∧
      (∀ a : S.infinityNormalizationRing pm,
        W.valuation (S.infinityNormalizationAmbientMap pm a) < 1 ↔ a ∈ q.1) :=
  NormalizationPrimeValuation.exists_ambient_valuation
    (S.infinityNormalizationField pm).val.toRingHom (S.infinityFiberHeightOne pm q)

/-- An actual ambient valuation extending the valuation at the chosen infinity prime. -/
def infinityAmbientValuation (pm : Bool) (q : S.infinityFiber pm) :
    ValuationSubring (Genuine.Ω S.prime.EK) :=
  (S.infinityAmbientValuation_exists pm q).choose

theorem infinityAmbientValuation_coordinate_mem (pm : Bool) (q : S.infinityFiber pm)
    (a : S.infinityNormalizationRing pm) :
    S.infinityNormalizationAmbientMap pm a ∈ S.infinityAmbientValuation pm q :=
  (S.infinityAmbientValuation_exists pm q).choose_spec.1 a

/-- The chosen infinity prime is exactly the center on the actual normalization ring. -/
theorem infinityAmbientValuation_center (pm : Bool) (q : S.infinityFiber pm)
    (a : S.infinityNormalizationRing pm) :
    (S.infinityAmbientValuation pm q).valuation (S.infinityNormalizationAmbientMap pm a) < 1 ↔
      a ∈ q.1 :=
  (S.infinityAmbientValuation_exists pm q).choose_spec.2 a

theorem infinityAmbientValuation_constant_mem (pm : Bool) (q : S.infinityFiber pm)
    (c : ↥S.prime.torsionField) :
    algebraMap (↥S.prime.torsionField) (Genuine.Ω S.prime.EK) c ∈
      S.infinityAmbientValuation pm q :=
  S.infinityAmbientValuation_coordinate_mem pm q
    (algebraMap (↥S.prime.torsionField) (S.infinityNormalizationRing pm) c)

theorem infinityAmbientValuation_inverseCoordinate_lt_one
    (pm : Bool) (q : S.infinityFiber pm) :
    (S.infinityAmbientValuation pm q).valuation ((Genuine.xG S.prime.EK)⁻¹) < 1 := by
  let a : S.infinityNormalizationRing pm :=
    algebraMap S.infinityPolynomialBase (S.infinityNormalizationRing pm) S.infinityCoordinate
  have ha : a ∈ q.1 := by
    change S.infinityCoordinate ∈ q.1.under S.infinityPolynomialBase
    rw [← q.2.2.over]
    exact S.infinityCoordinate_mem_baseIdeal
  have h := (S.infinityAmbientValuation_center pm q a).mpr ha
  change (S.infinityAmbientValuation pm q).valuation
    (S.infinityCoordinate : Genuine.Ω S.prime.EK) < 1 at h
  rwa [S.coe_infinityCoordinate] at h

/-- The original affine x-coordinate is excluded from every produced boundary valuation ring. -/
theorem infinityAmbientValuation_xG_not_mem (pm : Bool) (q : S.infinityFiber pm) :
    Genuine.xG S.prime.EK ∉ S.infinityAmbientValuation pm q := by
  have h := (S.infinityAmbientValuation pm q).mem_nonunits_iff.mpr
    (S.infinityAmbientValuation_inverseCoordinate_lt_one pm q)
  exact ((S.infinityAmbientValuation pm q).inv_mem_nonunits_iff.mp h).resolve_left
    (Genuine.transcendental_xG S.prime.EK).ne_zero

/-- The same unsigned ambient valuation contains the actual signed normalization image. -/
theorem infinityAmbientValuation_signed_coordinate_mem (q : S.infinityFiber false)
    (a : S.infinityNormalizationRing true) :
    S.infinityNormalizationAmbientMap true a ∈ S.infinityAmbientValuation false q := by
  have h := S.infinityAmbientValuation_coordinate_mem false q (S.infinityNormalizationRingMap a)
  change ((S.infinityNormalizationRingMap a : S.infinityNormalizationField false) :
    Genuine.Ω S.prime.EK) ∈ S.infinityAmbientValuation false q at h
  rw [S.coe_infinityNormalizationRingMap] at h
  exact h

/-- Its signed center is the original fiber map of the same unsigned prime. -/
theorem infinityAmbientValuation_signed_center (q : S.infinityFiber false)
    (a : S.infinityNormalizationRing true) :
    (S.infinityAmbientValuation false q).valuation (S.infinityNormalizationAmbientMap true a) < 1 ↔
      a ∈ (S.infinityFiberMap q).1 :=
  valuation_center_comap (S.infinityAmbientValuation false q)
    S.infinityNormalizationRingMap.toRingHom (S.infinityNormalizationAmbientMap true)
    (S.infinityNormalizationAmbientMap false) (fun b => S.coe_infinityNormalizationRingMap b)
    q.1 (S.infinityFiberMap q).1 (S.infinityFiberMap_asIdeal q)
    (S.infinityAmbientValuation_center false q) a

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
