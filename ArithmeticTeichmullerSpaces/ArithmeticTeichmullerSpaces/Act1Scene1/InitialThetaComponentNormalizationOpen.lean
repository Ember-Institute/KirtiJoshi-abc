import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaNormalizationTensor
import ArithmeticTeichmullerSpaces.Act1Scene1.FiniteBirationalLocalization

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); the actual normalization integral closure
and the proved tensor-component fraction field.
fidelity: the finite normalization map from the selected tensor component
to the actual unsigned normalization is an isomorphism after one nonzero
principal open of the component. The open is obtained from the common
fraction field and the finite extension denominator lemma.
boundary: Scene1/Derived. This is an ordinary affine normalization comparison.
It does not identify this open with the paper locus or prove the orbicurve
cartesian law.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open CategoryTheory AlgebraicGeometry
open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

local instance componentToNormalizationAlgebra :
    Algebra S.normalizationTensorComponentRing (S.coverNormalizationRing false) :=
  S.normalizationToTensorComponentRingMap.toAlgebra

local instance normalizationToFieldAlgebra :
    Algebra (S.coverNormalizationRing false)
      (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false) := inferInstance

local instance componentToFieldAlgebra :
    Algebra S.normalizationTensorComponentRing
      (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false) :=
  S.normalizationTensorComponentFieldAlgebra

local instance componentToNormalizationTower :
    IsScalarTower S.normalizationTensorComponentRing
      (S.coverNormalizationRing false)
      (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false) :=
  IsScalarTower.of_algebraMap_eq fun a => by
    simpa only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply] using
      congrArg (fun f : S.normalizationTensorComponentRing →+*
        (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false) => f a)
        S.normalizationTensorComponentFieldMap_eq_comp

local instance componentToNormalizationFinite :
    Module.Finite S.normalizationTensorComponentRing (S.coverNormalizationRing false) :=
  S.normalizationToTensorComponentRingMap_finite

local instance componentToNormalizationDomain :
    IsDomain (S.coverNormalizationRing false) := inferInstance

local instance componentFractionRing :
    IsFractionRing S.normalizationTensorComponentRing
      (Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false) :=
  S.normalizationTensorComponent_fractionField

set_option maxHeartbeats 1000000 in
theorem normalizationToTensorComponentScheme_exists_iso_basicOpen :
    ∃ d : S.normalizationTensorComponentRing, d ≠ 0 ∧ IsIso
      (Spec.map (CommRingCat.ofHom S.normalizationToTensorComponentRingMap) ∣_
        PrimeSpectrum.basicOpen d) := by
  let R := S.normalizationTensorComponentRing
  let A := S.coverNormalizationRing false
  let K := Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false
  letI : CommRing R := inferInstance
  letI : IsDomain R := inferInstance
  letI : CommRing A := inferInstance
  letI : Field K := inferInstance
  letI : Algebra R A := S.normalizationToTensorComponentRingMap.toAlgebra
  letI : Algebra R K := S.normalizationTensorComponentFieldAlgebra
  letI : Algebra A K := inferInstance
  letI : IsScalarTower R A K := IsScalarTower.of_algebraMap_eq fun a => by
    simpa only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply] using
      congrArg (fun f : R →+* K => f a) S.normalizationTensorComponentFieldMap_eq_comp
  letI : IsFractionRing R K := S.normalizationTensorComponent_fractionField
  letI : Module.Finite R A := S.normalizationToTensorComponentRingMap_finite
  have hAK : Function.Injective (algebraMap A K) := by
    intro x y h
    exact Subtype.ext h
  simpa only [R, A, K] using
    (@finite_extension_exists_basicOpen_iso R A K inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance hAK)

def normalizationComponentNormalizationOpen :
    S.normalizationTensorComponentScheme.Opens :=
  PrimeSpectrum.basicOpen
    (Classical.choose S.normalizationToTensorComponentScheme_exists_iso_basicOpen)

theorem normalizationComponentNormalizationOpen_nonempty :
    (S.normalizationComponentNormalizationOpen :
      Set S.normalizationTensorComponentScheme).Nonempty := by
  refine ⟨(⊥ : PrimeSpectrum S.normalizationTensorComponentRing), ?_⟩
  change Classical.choose S.normalizationToTensorComponentScheme_exists_iso_basicOpen ≠ 0
  exact (Classical.choose_spec S.normalizationToTensorComponentScheme_exists_iso_basicOpen).1

def normalizationComponentNormalizationOpenMap :
    (S.normalizationToTensorComponentScheme ⁻¹ᵁ
      S.normalizationComponentNormalizationOpen).toScheme ⟶
      S.normalizationComponentNormalizationOpen.toScheme :=
  S.normalizationToTensorComponentScheme ∣_
    S.normalizationComponentNormalizationOpen

instance isIso_normalizationComponentNormalizationOpenMap :
    IsIso S.normalizationComponentNormalizationOpenMap := by
  change IsIso (Spec.map (CommRingCat.ofHom S.normalizationToTensorComponentRingMap) ∣_
    PrimeSpectrum.basicOpen (Classical.choose S.normalizationToTensorComponentScheme_exists_iso_basicOpen))
  exact (Classical.choose_spec S.normalizationToTensorComponentScheme_exists_iso_basicOpen).2

instance finite_normalizationComponentNormalizationOpenMap :
    IsFinite S.normalizationComponentNormalizationOpenMap := inferInstance

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
