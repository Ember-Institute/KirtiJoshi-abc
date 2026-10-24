import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaNormalizationTensor
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaBaseNormalizationIsomorphisms
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the original normalization square and the signed base's proved polynomial model.
fidelity: identifies the tensor scheme with the actual fiber product of the
signed covering normalization and unsigned base normalization over the signed
base. The original unsigned covering map into this fiber product is finite,
and both projections are the original normalization maps.
boundary: Scene1/Derived. This identifies the ambient ordinary fiber product.
It does not assert that the unsigned covering scheme itself is the fiber
product, or provide the orbicurve cartesian law.
-/

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open scoped TensorProduct
universe u
noncomputable section

def tensorLeftRingMap {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] : A →+* A ⊗[R] B :=
  Algebra.TensorProduct.includeLeftRingHom

def tensorRightRingMap {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] : B →+* A ⊗[R] B :=
  Algebra.TensorProduct.includeRight.toRingHom

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
variable {F Z N : IntermediateField (rationalBase k t) Ω}

theorem tensorMap_comp_includeLeft (hF : F ≤ N) (hZ : Z ≤ N) :
    (normalizationTensorMap hF hZ).toRingHom.comp tensorLeftRingMap =
      (ringMap hF).toRingHom :=
  RingHom.ext fun a => (normalizationTensorMap_tmul hF hZ a 1).trans
    ((congrArg (fun x : coordRing t N => ringMap hF a * x) (map_one (ringMap hZ))).trans
      (mul_one _))

theorem tensorMap_comp_includeRight (hF : F ≤ N) (hZ : Z ≤ N) :
    (normalizationTensorMap hF hZ).toRingHom.comp tensorRightRingMap =
      (ringMap hZ).toRingHom :=
  RingHom.ext fun b => (normalizationTensorMap_tmul hF hZ 1 b).trans
    ((congrArg (fun x : coordRing t N => x * ringMap hZ b) (map_one (ringMap hF))).trans
      (one_mul _))

end
end JoshiTeich.Act1Scene1.FunctionFieldNormalization

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeierstrassCurve
open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical TensorProduct
universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] coverTensorBaseAlgebra coverTensorBaseSMul coverTensorBaseModule
  baseTensorBaseAlgebra baseTensorBaseSMul baseTensorBaseModule normalizationTensorCommRing
  tensorRingBaseAlgebra presentationCoefficientAlgebra basePresentationCoefficientAlgebra
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

local instance signedBaseTensorAlgebra :
    Algebra S.normalizationTensorBase (S.baseNormalizationRing true) :=
  FunctionFieldNormalization.coordRingBaseAlgebra (Genuine.normalizationField S.prime.EK 1 ⊥ true)
local instance signedBaseTensorSMul :
    SMul S.normalizationTensorBase (S.baseNormalizationRing true) :=
  (signedBaseTensorAlgebra S).toSMul
local instance signedBaseTensorModule :
    Module S.normalizationTensorBase (S.baseNormalizationRing true) :=
  (signedBaseTensorAlgebra S).toModule

def normalizationTensorLeftRingMap :
    S.coverNormalizationRing true →+* S.normalizationTensorRing :=
  FunctionFieldNormalization.tensorLeftRingMap (R := S.normalizationTensorBase)

def normalizationTensorRightRingMap :
    S.baseNormalizationRing false →+* S.normalizationTensorRing :=
  FunctionFieldNormalization.tensorRightRingMap (R := S.normalizationTensorBase)

def normalizationTensorToSignedCover :
    S.normalizationTensorScheme ⟶ S.coverNormalizationScheme true :=
  Spec.map (CommRingCat.ofHom S.normalizationTensorLeftRingMap)

def normalizationTensorToUnsignedBase :
    S.normalizationTensorScheme ⟶ S.baseNormalizationScheme false :=
  Spec.map (CommRingCat.ofHom S.normalizationTensorRightRingMap)

theorem normalizationTensorMap_comp_left :
    S.normalizationTensorMap.toRingHom.comp S.normalizationTensorLeftRingMap =
      S.signedCoverNormalizationRingMap.toRingHom :=
  FunctionFieldNormalization.tensorMap_comp_includeLeft
    (Genuine.normalizationField_signed_le_unsigned S.prime.EK S.prime.ℓ S.prime.M)
    (Genuine.normalization_base_unsigned_le S.prime.EK S.prime.ℓ S.prime.M)

theorem normalizationTensorMap_comp_right :
    S.normalizationTensorMap.toRingHom.comp S.normalizationTensorRightRingMap =
      (S.baseToCoverNormalizationRingMap false).toRingHom :=
  FunctionFieldNormalization.tensorMap_comp_includeRight
    (Genuine.normalizationField_signed_le_unsigned S.prime.EK S.prime.ℓ S.prime.M)
    (Genuine.normalization_base_unsigned_le S.prime.EK S.prime.ℓ S.prime.M)

theorem normalizationToTensorScheme_comp_left :
    S.normalizationToTensorScheme ≫ S.normalizationTensorToSignedCover =
      S.signedCoverNormalizationMap := by
  exact (Spec.map_comp (CommRingCat.ofHom S.normalizationTensorLeftRingMap)
    (CommRingCat.ofHom S.normalizationTensorMap.toRingHom)).symm.trans
      (congrArg (fun f : S.coverNormalizationRing true →+* S.coverNormalizationRing false =>
        Spec.map (CommRingCat.ofHom f)) S.normalizationTensorMap_comp_left)

theorem normalizationToTensorScheme_comp_right :
    S.normalizationToTensorScheme ≫ S.normalizationTensorToUnsignedBase =
      S.coverToBaseNormalizationMap false := by
  exact (Spec.map_comp (CommRingCat.ofHom S.normalizationTensorRightRingMap)
    (CommRingCat.ofHom S.normalizationTensorMap.toRingHom)).symm.trans
      (congrArg (fun f : S.baseNormalizationRing false →+* S.coverNormalizationRing false =>
        Spec.map (CommRingCat.ofHom f)) S.normalizationTensorMap_comp_right)

theorem normalizationTensorSquare_isPullback :
    IsPullback S.normalizationTensorToSignedCover S.normalizationTensorToUnsignedBase
      (S.coverToBaseNormalizationMap true) S.signedBaseNormalizationMap := by
  let e : CommRingCat.of S.normalizationTensorBase ≅
      CommRingCat.of (S.baseNormalizationRing true) :=
    (RingEquiv.ofBijective (algebraMap S.normalizationTensorBase (S.baseNormalizationRing true))
      (Genuine.signedBaseNormalization_algebraMap_bijective S.prime.EK)).toCommRingCatIso
  have ht := CommRingCat.isPushout_tensorProduct S.normalizationTensorBase
    (S.coverNormalizationRing true) (S.baseNormalizationRing false)
  have h : IsPushout
      (CommRingCat.ofHom (S.baseToCoverNormalizationRingMap true).toRingHom)
      (CommRingCat.ofHom S.signedBaseNormalizationRingMap.toRingHom)
      (CommRingCat.ofHom S.normalizationTensorLeftRingMap)
      (CommRingCat.ofHom S.normalizationTensorRightRingMap) := by
    refine ht.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      rfl
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      rfl
    · rfl
    · rfl
  exact isPullback_SpecMap_of_isPushout _ _ _ _ h

def normalizationTensorPullbackIso : S.normalizationTensorScheme ≅
    pullback (S.coverToBaseNormalizationMap true) S.signedBaseNormalizationMap :=
  S.normalizationTensorSquare_isPullback.isoPullback

theorem normalizationTensorPullbackIso_hom_fst :
    S.normalizationTensorPullbackIso.hom ≫ pullback.fst _ _ =
      S.normalizationTensorToSignedCover :=
  S.normalizationTensorSquare_isPullback.isoPullback_hom_fst

theorem normalizationTensorPullbackIso_hom_snd :
    S.normalizationTensorPullbackIso.hom ≫ pullback.snd _ _ =
      S.normalizationTensorToUnsignedBase :=
  S.normalizationTensorSquare_isPullback.isoPullback_hom_snd

def normalizationToPullbackScheme : S.coverNormalizationScheme false ⟶
    pullback (S.coverToBaseNormalizationMap true) S.signedBaseNormalizationMap :=
  pullback.lift S.signedCoverNormalizationMap (S.coverToBaseNormalizationMap false)
    S.normalizationMap_square.symm

theorem normalizationToTensorScheme_comp_pullbackIso :
    S.normalizationToTensorScheme ≫ S.normalizationTensorPullbackIso.hom =
      S.normalizationToPullbackScheme := by
  apply pullback.hom_ext
  · rw [Category.assoc, S.normalizationTensorPullbackIso_hom_fst]
    exact S.normalizationToTensorScheme_comp_left.trans (pullback.lift_fst _ _ _).symm
  · rw [Category.assoc, S.normalizationTensorPullbackIso_hom_snd]
    exact S.normalizationToTensorScheme_comp_right.trans (pullback.lift_snd _ _ _).symm

instance finite_normalizationToPullbackScheme : IsFinite S.normalizationToPullbackScheme := by
  rw [← S.normalizationToTensorScheme_comp_pullbackIso]
  infer_instance

theorem normalizationTensorComponent_birationalOver_pullback :
    Scheme.BirationalOver S.normalizationToPullbackScheme
      (S.tensorComponentToTensorScheme ≫ S.normalizationTensorPullbackIso.hom) := by
  obtain ⟨e, he⟩ := S.normalizationToTensorComponentScheme_birationalOver
  refine ⟨e, ?_⟩
  have h := congrArg (fun f : e.source.toScheme ⟶ S.normalizationTensorScheme =>
    f ≫ S.normalizationTensorPullbackIso.hom) he
  simpa only [Scheme.PartialIso.IsOver, Category.assoc,
    S.normalizationToTensorScheme_comp_pullbackIso] using h

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
