/-
Source: Pi1/Orbicurve/Lefschetz.lean (`CoreStar`, `coreStar_iff_sOmega`,
and `sOmega_iff_sOmegaTY`) at revision ca7def953193f861a462aa0831eec8f0a31ff69f.
Original author: Christian Merten and the pi1 contributors.
License: Apache-2.0.
-/
import Solutions.Source_ReferenceIutCanLiftQuadraticModel
import Solutions.Source_ReferenceIutCanLiftDescendedCover
import Solutions.Source_ReferenceIutCanLiftCoreCriterion

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open Ideal Polynomial WeierstrassCurve JoshiTeich.Act1Scene1
open JoshiTeich.Act1Scene1.AffineOrbicurvePresentation
open JoshiTeich.Act1Scene1.FunctionFieldNormalization
open JoshiTeich.ReferenceIut.Anabelian.Genuine
open scoped IntermediateField.algebraAdjoinAdjoin

universe u

noncomputable section

variable {k Ω : Type u} [Field k] [hCharZero : CharZero k] [Field Ω] [Algebra k Ω]
  [hClosed : IsAlgClosed Ω]
variable (E : WeierstrassCurve k) [hElliptic : E.IsElliptic]

local notation "U" => normalizationPresentation E 1 ⊥ false
local notation "S" => normalizationPresentation E 1 ⊥ true

/-- Uniqueness of a morphism to the sign quotient on every cover of the actual unsigned model. -/
def NormalizationCoreStar : Prop :=
  ∀ Z : AffineOrbicurvePresentation k, Cover Z U → Subsingleton (Cover Z S)

theorem normalizationCoreStar_of_isCoreOf (h : IsCoreOf U S) : NormalizationCoreStar E := by
  intro Z φ
  exact (h.2 Z ⟨Z, ⟨φ⟩, ⟨Cover.id Z⟩⟩).2

/-- Uniqueness on covers gives the core property for the actual signed normalization. -/
theorem normalizationIsCore_of_normalizationCoreStar (h : NormalizationCoreStar E) : IsCoreOf U S :=
  isCoreOf_of_unique_covers (signedNormalizationCover E 1 ⊥) (fun _ _ => rfl) h

private theorem comap_equiv_square {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (eA : A ≃+* A') (eB : B ≃+* B') (f : A →+* B) (g : A' →+* B')
    (h : ∀ a, g (eA a) = eB (f a)) (w : Ideal B') :
    (w.comap g).comap eA.toRingHom = (w.comap eB.toRingHom).comap f := by
  ext a
  change g (eA a) ∈ w ↔ eB (f a) ∈ w
  rw [h a]

private theorem ramificationIdx_equiv_square {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [IsDedekindDomain B] [IsDedekindDomain A'] [IsDomain B']
    (eA : A ≃+* A') (eB : B ≃+* B') (f : A →+* B) (g : A' →+* B')
    (hg : Function.Injective g) (h : ∀ a, g (eA a) = eB (f a)) (w : Ideal B') [w.IsPrime] :
    (letI := g.toAlgebra; w.ramificationIdx A') =
      (letI := f.toAlgebra; (w.comap eB.toRingHom).ramificationIdx A) := by
  have hcomp : g.comp eA.toRingHom = eB.toRingHom.comp f := RingHom.ext h
  exact (ramificationIdx_equiv_comp eA g hg w).symm.trans
    ((ramificationIdx_congr hcomp w).trans (ramificationIdx_comp_equiv f eB w))

private def coverOfTargetEquiv {Z X : AffineOrbicurvePresentation k}
    {R : Type u} [CommRing R] [Algebra k R] [IsDedekindDomain R]
    (e : X.A ≃ₐ[k] R) (g : R →ₐ[k] Z.A) (hgi : Function.Injective g)
    (hint : g.toRingHom.IsIntegral)
    (hram : ∀ w : Ideal Z.A, w.IsMaximal →
      (letI := g.toRingHom.toAlgebra; w.ramificationIdx R) * Z.mult w =
        X.mult ((w.comap g.toRingHom).comap e.toRingEquiv.toRingHom)) : Cover Z X where
  f := g.comp e.toAlgHom
  injective := hgi.comp e.injective
  isIntegral := RingHom.IsIntegral.trans e.toRingEquiv.toRingHom g.toRingHom
    (RingHom.isIntegral_of_surjective _ e.surjective) hint
  ramification w hw := by
    letI : w.IsPrime := hw.isPrime
    have he := ramificationIdx_equiv_comp e.toRingEquiv g.toRingHom hgi w
    exact (congrArg (fun n => n * Z.mult w) he).trans (hram w hw)

private theorem ramification_of_cover_equiv_square {Z X : AffineOrbicurvePresentation k}
    {R A : Type u} [CommRing R] [Algebra k R] [IsDedekindDomain R]
    [CommRing A] [Algebra k A] [IsDomain A]
    (eX : X.A ≃ₐ[k] R) (eZ : Z.A ≃ₐ[k] A) (φ : Cover Z X) (g : R →ₐ[k] A)
    (hgi : Function.Injective g) (hcomm : ∀ a : X.A, g (eX a) = eZ (φ.f a))
    (hZ : ∀ q : Ideal Z.A, q.IsMaximal → Z.mult q = 1)
    (w : Ideal A) (hw : w.IsMaximal) :
    (letI := g.toRingHom.toAlgebra; w.ramificationIdx R) =
      X.mult ((w.comap g.toRingHom).comap eX.toRingEquiv.toRingHom) := by
  letI : w.IsPrime := hw.isPrime
  let q : Ideal Z.A := w.comap eZ.toRingEquiv.toRingHom
  have hq : q.IsMaximal := Ideal.comap_isMaximal_of_equiv eZ.toRingEquiv
  have hram := φ.ramification q hq
  rw [hZ q hq, mul_one] at hram
  have hc := comap_equiv_square eX.toRingEquiv eZ.toRingEquiv φ.f.toRingHom
    g.toRingHom hcomm w
  have he := ramificationIdx_equiv_square eX.toRingEquiv eZ.toRingEquiv φ.f.toRingHom
    g.toRingHom hgi hcomm w
  exact he.trans (hram.trans (congrArg X.mult hc.symm))

variable (j : E.toAffine.FunctionField →ₐ[k] Ω)

local notation "t" => j (xF E)
local notation "y" => j (yF E)
local notation "B" => rationalBase k t
local notation "N" => quadraticParameterField k t y
local notation "T" => (⊥ : IntermediateField B Ω)

private def unsignedNormalizationEquiv : (U).A ≃ₐ[k] coordRing t N :=
  unsignedQuadraticModelEquiv E j

private def signedNormalizationEquiv : (S).A ≃ₐ[k] coordRing t T :=
  signedQuadraticModelEquiv E j

private theorem quadraticNormalization_square (a : (S).A) :
    unsignedNormalizationEquiv E j ((signedNormalizationCover E 1 ⊥).f a) =
      ringMap (bot_le : T ≤ N) (signedNormalizationEquiv E j a) :=
  quadraticModelEquiv_square E j a

private theorem quadraticModel_finiteDimensional : FiniteDimensional B N :=
  finiteDimensional_quadraticParameterField (weierstrassQuadraticB_mem E t)
    (weierstrassQuadraticC_mem E t) (functionField_quadratic E j)

private theorem quadraticModel_dedekind {F : IntermediateField B Ω} [FiniteDimensional B F] :
    IsDedekindDomain (coordRing t F) := by
  letI : CharZero B := charZero_of_injective_algebraMap (algebraMap k B).injective
  letI : Algebra.IsSeparable B F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact dedekindRing t (transcendental_functionField_x E j) F

include hClosed in
private theorem signedQuadraticModel_mult_eq (v : Ideal (coordRing t T)) (hv : v.IsMaximal) :
    (S).mult (v.comap (signedNormalizationEquiv E j).toRingEquiv.toRingHom) =
      signQuotientMultiplicity t y v := by
  letI : FiniteDimensional B N := quadraticModel_finiteDimensional E j
  letI : IsGalois B N := isGalois_quadraticParameterField (weierstrassQuadraticB_mem E t)
    (weierstrassQuadraticC_mem E t) (functionField_quadratic E j)
  letI : IsDedekindDomain (coordRing t T) := quadraticModel_dedekind E j
  let eS : (S).A ≃ₐ[k] coordRing t T := signedNormalizationEquiv E j
  let eU : (U).A ≃ₐ[k] coordRing t N := unsignedNormalizationEquiv E j
  let π : Cover U S := signedNormalizationCover E 1 ⊥
  let f : coordRing t T →ₐ[k] coordRing t N := ringMap (bot_le : T ≤ N)
  have hcomm (a : (S).A) : f (eS a) = eU (π.f a) :=
    (quadraticNormalization_square E j a).symm
  obtain ⟨w, hw, hwv⟩ := normalization_exists_maximal_over (bot_le : T ≤ N) v hv
  have hram := ramification_of_cover_equiv_square eS eU π f
    (ringMap_injective (bot_le : T ≤ N)) hcomm (fun _ _ => rfl) w hw
  have hsign := signQuotientMultiplicity_eq_index (transcendental_functionField_x E j) w hw
  have h₁ : (letI := f.toRingHom.toAlgebra; w.ramificationIdx (coordRing t T)) =
      (S).mult (v.comap eS.toRingEquiv.toRingHom) :=
    hram.trans (congrArg (fun q : Ideal (coordRing t T) =>
      (S).mult (q.comap eS.toRingEquiv.toRingHom)) hwv)
  have h₂ : ramificationIndex (bot_le : T ≤ N) w = signQuotientMultiplicity t y v :=
    hsign.trans (congrArg (signQuotientMultiplicity t y) hwv)
  exact h₁.symm.trans h₂

private def unramifiedQuadraticModel {F : IntermediateField B Ω} [FiniteDimensional B F] :
    AffineOrbicurvePresentation k := by
  letI : CharZero B := charZero_of_injective_algebraMap (algebraMap k B).injective
  letI : Algebra.IsSeparable B F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  let ht := transcendental_functionField_x E j
  exact {
    A := coordRing t F
    isDedekindDomain := dedekindRing t ht F
    finiteType := finiteTypeRing t ht F
    not_isField := notFieldRing t ht F
    mult := fun _ => 1
    mult_pos := fun _ _ => Nat.one_pos
    finite_mult := by simp
  }

private theorem ringMap_bot_trans {F L : IntermediateField B Ω} (h : F ≤ L) (a : coordRing t T) :
    ringMap h (ringMap (bot_le : T ≤ F) a) = ringMap (bot_le : T ≤ L) a :=
  Subtype.ext (Subtype.ext rfl)

private def unsignedModelCover {L : IntermediateField B Ω} [FiniteDimensional B L]
    (hNL : N ≤ L) (hUnram : ∀ w : Ideal (coordRing t L), w.IsMaximal →
      ramificationIndex hNL w = 1) : Cover (unramifiedQuadraticModel E j (F := L)) U := by
  letI : FiniteDimensional B N := quadraticModel_finiteDimensional E j
  letI : IsDedekindDomain (coordRing t N) := quadraticModel_dedekind E j
  exact coverOfTargetEquiv (unsignedNormalizationEquiv E j) (ringMap hNL)
    (ringMap_injective hNL) (ringMap_isIntegral hNL) fun w hw =>
      (Nat.mul_one _).trans (hUnram w hw)

include hClosed in
private def signedModelCover {L : IntermediateField B Ω} [FiniteDimensional B L]
    (g : coordRing t T →ₐ[k] coordRing t L) (hgi : Function.Injective g)
    (hint : g.toRingHom.IsIntegral) (hram : ∀ w : Ideal (coordRing t L), w.IsMaximal →
      (letI := g.toRingHom.toAlgebra; w.ramificationIdx (coordRing t T)) =
        signQuotientMultiplicity t y (w.comap g)) :
    Cover (unramifiedQuadraticModel E j (F := L)) S := by
  letI : IsDedekindDomain (coordRing t T) := quadraticModel_dedekind E j
  let eS : (S).A ≃ₐ[k] coordRing t T := signedNormalizationEquiv E j
  refine coverOfTargetEquiv eS g hgi hint ?_
  intro w hw
  change Ideal (coordRing t L) at w
  change w.IsMaximal at hw
  letI : w.IsMaximal := hw
  have hv : (w.comap g.toRingHom).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' g.toRingHom hint w
  exact (Nat.mul_one _).trans ((hram w hw).trans
    (signedQuadraticModel_mult_eq E j _ hv).symm)

include hClosed in
/-- Core uniqueness on the actual curve gives the quadratic-field criterion in `Ω`. -/
theorem quadraticCoverRigidity_of_normalizationCoreStar (h : NormalizationCoreStar E) :
    QuadraticCoverRigidity k t y := by
  intro L hLdim hNL hUnram g hgi hgintegral hg
  letI : FiniteDimensional B L := hLdim
  let Z := unramifiedQuadraticModel E j (F := L)
  let eU : (U).A ≃ₐ[k] coordRing t N := unsignedNormalizationEquiv E j
  let eS : (S).A ≃ₐ[k] coordRing t T := signedNormalizationEquiv E j
  let π : Cover U S := signedNormalizationCover E 1 ⊥
  let φ : Cover Z U := unsignedModelCover E j hNL hUnram
  let ψ : Cover Z S := signedModelCover E j g hgi hgintegral hg
  have heq : ψ = φ.comp π := (h Z φ).elim ψ (φ.comp π)
  apply AlgHom.ext
  intro a
  obtain ⟨b, rfl⟩ := eS.surjective a
  have hb : g (eS b) = ringMap hNL (eU (π.f b)) :=
    congrArg (fun f : Cover Z S => f.f b) heq
  exact hb.trans ((congrArg (ringMap hNL) (quadraticNormalization_square E j b)).trans
    (ringMap_bot_trans E j hNL (eS b)))

include hClosed in
private theorem signedCover_eq_of_quadraticCoverRigidity (h : QuadraticCoverRigidity k t y)
    {Z : AffineOrbicurvePresentation k} (φ : Cover Z U) (ψ : Cover Z S)
    (hZ : ∀ q : Ideal Z.A, q.IsMaximal → Z.mult q = 1)
    {L : IntermediateField B Ω} [FiniteDimensional B L] (hNL : N ≤ L)
    (hUnram : ∀ w : Ideal (coordRing t L), w.IsMaximal → ramificationIndex hNL w = 1)
    (eZ : Z.A ≃ₐ[k] coordRing t L)
    (hCommφ : ∀ a : (U).A, ringMap hNL (unsignedNormalizationEquiv E j a) = eZ (φ.f a)) :
    ψ = φ.comp (signedNormalizationCover E 1 ⊥) := by
  letI : IsDedekindDomain (coordRing t T) := quadraticModel_dedekind E j
  let eS : (S).A ≃ₐ[k] coordRing t T := signedNormalizationEquiv E j
  let g : coordRing t T →ₐ[k] coordRing t L := eZ.toAlgHom.comp (ψ.f.comp eS.symm.toAlgHom)
  have hgi : Function.Injective g := eZ.injective.comp (ψ.injective.comp eS.symm.injective)
  have hgintegral : g.toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _
    (RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ eS.symm.surjective)
      ψ.isIntegral) (RingHom.isIntegral_of_surjective _ eZ.surjective)
  have hCommψ (a : (S).A) : g (eS a) = eZ (ψ.f a) :=
    congrArg (fun b : (S).A => eZ (ψ.f b)) (eS.symm_apply_apply a)
  have hram (w : Ideal (coordRing t L)) (hw : w.IsMaximal) :
      (letI := g.toRingHom.toAlgebra; w.ramificationIdx (coordRing t T)) =
        signQuotientMultiplicity t y (w.comap g) := by
    letI : w.IsMaximal := hw
    have hv : (w.comap g.toRingHom).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' g.toRingHom hgintegral w
    exact (ramification_of_cover_equiv_square eS eZ ψ g hgi hCommψ hZ w hw).trans
      (signedQuadraticModel_mult_eq E j _ hv)
  have hg := h L hNL hUnram g hgi hgintegral hram
  let π : Cover U S := signedNormalizationCover E 1 ⊥
  apply Cover.ext_f
  apply AlgHom.ext
  intro a
  apply eZ.injective
  change eZ (ψ.f a) = eZ (φ.f (π.f a))
  calc
    eZ (ψ.f a) = g (eS a) := (hCommψ a).symm
    _ = ringMap (bot_le : T ≤ L) (eS a) := AlgHom.congr_fun hg _
    _ = ringMap hNL (ringMap (bot_le : T ≤ N) (eS a)) :=
      (ringMap_bot_trans E j hNL _).symm
    _ = ringMap hNL (unsignedNormalizationEquiv E j (π.f a)) :=
      (congrArg (ringMap hNL) (quadraticNormalization_square E j a)).symm
    _ = eZ (φ.f (π.f a)) := hCommφ (π.f a)

include hClosed in
/-- The criterion in `Ω` gives core uniqueness on all covers of the actual unsigned model. -/
theorem normalizationCoreStar_of_quadraticCoverRigidity (h : QuadraticCoverRigidity k t y) :
    NormalizationCoreStar E := by
  intro Z φ
  letI : FiniteDimensional B N := quadraticModel_finiteDimensional E j
  letI : IsDedekindDomain (coordRing t N) := quadraticModel_dedekind E j
  let eU : (U).A ≃ₐ[k] coordRing t N := unsignedNormalizationEquiv E j
  let f : coordRing t N →ₐ[k] Z.A := φ.f.comp eU.symm.toAlgHom
  have hfi : f.toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _
    (RingHom.isIntegral_of_surjective _ eU.symm.surjective) φ.isIntegral
  obtain ⟨L, hLdim, hNL, eZ, heZ⟩ := exists_algEquiv_coordRing t Z.A f
    (φ.injective.comp eU.symm.injective) hfi
  letI : FiniteDimensional B L := hLdim
  have hCommφ (a : (U).A) : ringMap hNL (eU a) = eZ (φ.f a) :=
    (heZ (eU a)).symm.trans
      (congrArg (fun b : (U).A => eZ (φ.f b)) (eU.symm_apply_apply a))
  have hZ (q : Ideal Z.A) (hq : q.IsMaximal) : Z.mult q = 1 := by
    have hram := φ.ramification q hq
    change _ * Z.mult q = 1 at hram
    exact Nat.eq_one_of_mul_eq_one_left hram
  have hUnram (w : Ideal (coordRing t L)) (hw : w.IsMaximal) : ramificationIndex hNL w = 1 :=
    (ramification_of_cover_equiv_square eU eZ φ (ringMap hNL) (ringMap_injective hNL)
      hCommφ hZ w hw).trans rfl
  have hCanonical (ψ : Cover Z S) : ψ = φ.comp (signedNormalizationCover E 1 ⊥) :=
    signedCover_eq_of_quadraticCoverRigidity E j h φ ψ hZ hNL hUnram eZ hCommφ
  exact ⟨fun a b => (hCanonical a).trans (hCanonical b).symm⟩

include hClosed in
/-- Compare core uniqueness with the original quadratic coordinates in any algebraically
closed ambient field. -/
theorem normalizationCoreStar_iff_quadraticCoverRigidity :
    NormalizationCoreStar E ↔ QuadraticCoverRigidity k t y :=
  ⟨quadraticCoverRigidity_of_normalizationCoreStar E j,
    normalizationCoreStar_of_quadraticCoverRigidity E j⟩

end

end AbcAdaptation.Reference.Iut.Anabelian
