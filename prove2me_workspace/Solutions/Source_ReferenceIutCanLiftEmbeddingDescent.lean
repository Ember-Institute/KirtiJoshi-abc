/-
Source: Pi1/Orbicurve/Lefschetz.lean (coreStar_of_map) at revision
ca7def953193f861a462aa0831eec8f0a31ff69f.
Original author: Christian Merten and the pi1 contributors.
License: Apache-2.0.
-/
import Solutions.Source_ReferenceIutCanLiftCoreStar
import Solutions.Source_ReferenceIutCanLiftExtendedCover

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open WeierstrassCurve
open JoshiTeich.Act1Scene1.AffineOrbicurvePresentation (IsCoreOf)
open JoshiTeich.Act1Scene1.FunctionFieldNormalization
open JoshiTeich.ReferenceIut.Anabelian.Genuine (xF yF normalizationPresentation)

universe u

/-- The core property of the actual sign normalization descends along a field embedding. -/
theorem normalizationIsCore_of_map {k K : Type u} [Field k] [Field K] [CharZero k] [CharZero K]
    (f : k →+* K) (E : WeierstrassCurve k) [E.IsElliptic]
    (hK : IsCoreOf (normalizationPresentation (E.map f) 1 ⊥ false)
      (normalizationPresentation (E.map f) 1 ⊥ true)) :
    IsCoreOf (normalizationPresentation E 1 ⊥ false) (normalizationPresentation E 1 ⊥ true) := by
  letI algebrakK : Algebra k K := f.toAlgebra
  let E' := E.map f
  let Ω := AlgebraicClosure E'.toAffine.FunctionField
  letI algebraKΩ : Algebra K Ω := inferInstance
  letI algebrakΩ : Algebra k Ω := ((algebraMap K Ω).comp f).toAlgebra
  letI : SMul k K := algebrakK.toSMul
  letI : SMul K Ω := algebraKΩ.toSMul
  letI : SMul k Ω := algebrakΩ.toSMul
  letI : IsScalarTower k K Ω :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := K) (A := Ω) fun _ => rfl
  let jK : E'.toAffine.FunctionField →ₐ[K] Ω := IsScalarTower.toAlgHom K E'.toAffine.FunctionField Ω
  let t := jK (xF E')
  let y := jK (yF E')
  have htK : Transcendental K t := transcendental_functionField_x E' jK
  have ht : Transcendental k t := transcendental_of_constantExtension htK
  have hy : y ^ 2 + weierstrassQuadraticB E t * y = weierstrassQuadraticC E t := by
    rw [← weierstrassQuadraticB_map (K := K) E t, ← weierstrassQuadraticC_map (K := K) E t]
    exact functionField_quadratic E' jK
  have hRigK : QuadraticCoverRigidity K t y :=
    quadraticCoverRigidity_of_normalizationCoreStar E' jK (normalizationCoreStar_of_isCoreOf E' hK)
  have hRig : QuadraticCoverRigidity k t y :=
    quadraticCoverRigidity_of_constantExtension htK (weierstrassQuadraticB_mem E t)
      (weierstrassQuadraticC_mem E t) hy hRigK
  obtain ⟨j, hx, hY⟩ := exists_functionField_embedding_of_quadratic E ht hy
  apply normalizationIsCore_of_normalizationCoreStar E
  apply normalizationCoreStar_of_quadraticCoverRigidity E j
  rw [hx, hY]
  exact hRig

end AbcAdaptation.Reference.Iut.Anabelian
