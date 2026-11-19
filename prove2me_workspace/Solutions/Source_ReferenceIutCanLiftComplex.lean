/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original paths OrbicurveCores/U2/{Statement,CoreMap,Assembly}.lean
-/
import Solutions.Source_ReferenceIutCanLiftPresentation
import Solutions.Source_ReferenceIutCanLiftCoverDescent
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedBaseNormalizationRing

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open WeierstrassCurve Polynomial JoshiTeich.Act1Scene1
open JoshiTeich.Act1Scene1.AffineOrbicurvePresentation
open JoshiTeich.ReferenceIut.Anabelian.Genuine

/-- The `x`-coordinate in the level-one unsigned normalization ring. -/
noncomputable def normalizationBaseX {k : Type*} [Field k] [CharZero k]
    (E : WeierstrassCurve k) [E.IsElliptic] : (normalizationPresentation E 1 ⊥ false).A :=
  signedNormalizationRingMap E 1 ⊥ (signedBasePolynomialAlgEquiv E X)

/-- Theorem G on the actual normalization rings. -/
def CanLift27ComplexXDescends : Prop :=
  ∀ (E : WeierstrassCurve ℂ) [E.IsElliptic], (∀ c ∈ canLiftExceptionalJ, E.j ≠ (c : ℂ)) →
    ∀ {Y Z : AffineOrbicurvePresentation ℂ},
      (φ : Cover Z (normalizationPresentation E 1 ⊥ false)) → (ψ : Cover Z Y) →
      ∃ y : Y.A, ψ.f y = φ.f (normalizationBaseX E)

/-- The uniqueness part on finite étale covers of the once-punctured curve. -/
def CanLift27ComplexUniqueCover : Prop :=
  ∀ (E : WeierstrassCurve ℂ) [E.IsElliptic], (∀ c ∈ canLiftExceptionalJ, E.j ≠ (c : ℂ)) →
    ∀ Z : AffineOrbicurvePresentation ℂ, Cover Z (normalizationPresentation E 1 ⊥ false) →
      Subsingleton (Cover Z (normalizationPresentation E 1 ⊥ true))

/-- Every self-cover of the punctured sign quotient is the identity away from `j = 0, 1728`. -/
def CanLift27ComplexHemiRigid : Prop :=
  ∀ (E : WeierstrassCurve ℂ) [E.IsElliptic], E.j ≠ 0 → E.j ≠ 1728 →
    ∀ f : Cover (normalizationPresentation E 1 ⊥ true) (normalizationPresentation E 1 ⊥ true),
      f = Cover.id _

private theorem factor_signQuotient (hdesc : CanLift27ComplexXDescends)
    (E : WeierstrassCurve ℂ) [E.IsElliptic] (hj : ∀ c ∈ canLiftExceptionalJ, E.j ≠ (c : ℂ))
    {Y Z : AffineOrbicurvePresentation ℂ} (φ : Cover Z (normalizationPresentation E 1 ⊥ false))
    (ψ : Cover Z Y) : ∃ f : Cover Y (normalizationPresentation E 1 ⊥ true),
      ψ.comp f = φ.comp (signedNormalizationCover E 1 ⊥) := by
  let X₀ := normalizationPresentation E 1 ⊥ false
  let C := normalizationPresentation E 1 ⊥ true
  let π : Cover X₀ C := signedNormalizationCover E 1 ⊥
  obtain ⟨y, hy⟩ := hdesc E hj φ ψ
  let e : ℂ[X] ≃ₐ[ℂ] C.A := signedBasePolynomialAlgEquiv E
  let g : C.A →ₐ[ℂ] Y.A := (aeval y).comp e.symm.toAlgHom
  let χ := φ.comp π
  have hg : ψ.f.comp g = χ.f := by
    have he : (ψ.f.comp g).comp e.toAlgHom = χ.f.comp e.toAlgHom := by
      apply Polynomial.algHom_ext
      change ψ.f (aeval y (e.symm (e X))) = φ.f (π.f (e X))
      rw [AlgEquiv.symm_apply_apply, aeval_X]
      exact hy
    apply AlgHom.ext
    intro c
    obtain ⟨p, rfl⟩ := e.surjective c
    exact AlgHom.congr_fun he p
  exact ⟨Cover.descend ψ χ g hg, Cover.ext_f hg⟩

/-- Assemble the complex core theorem from descent of `x` and uniqueness on covers. -/
theorem canLift27Complex_of_xDescends_and_uniqueCover
    (hdesc : CanLift27ComplexXDescends) (huniq : CanLift27ComplexUniqueCover) :
    CanLift27Complex := by
  intro E _ hj
  let X₀ := normalizationPresentation E 1 ⊥ false
  let C := normalizationPresentation E 1 ⊥ true
  let π : Cover X₀ C := signedNormalizationCover E 1 ⊥
  refine ⟨⟨X₀, ⟨Cover.id X₀⟩, ⟨π⟩⟩, ?_⟩
  intro Y hY
  obtain ⟨Z, ⟨φ⟩, ⟨ψ⟩⟩ := hY
  obtain ⟨f, _⟩ := factor_signQuotient hdesc E hj φ ψ
  refine ⟨⟨f⟩, ⟨?_⟩⟩
  intro a b
  apply Cover.ext_f
  apply AlgHom.ext
  intro c
  apply ψ.injective
  exact congrArg (fun f : Cover Z C => f.f c) ((huniq E hj Z φ).elim (ψ.comp a) (ψ.comp b))

/-- Theorem G and rigidity of the punctured sign quotient give uniqueness on every cover. -/
theorem canLift27ComplexUniqueCover_of_xDescends_and_hemiRigid
    (hdesc : CanLift27ComplexXDescends) (hrigid : CanLift27ComplexHemiRigid) :
    CanLift27ComplexUniqueCover := by
  intro E _ hj Z φ
  have hj0 : E.j ≠ 0 := by simpa using hj 0 (by simp [canLiftExceptionalJ])
  have hj1728 : E.j ≠ 1728 := by simpa using hj 1728 (by simp [canLiftExceptionalJ])
  let C := normalizationPresentation E 1 ⊥ true
  have h : ∀ ψ : Cover Z C, ψ = φ.comp (signedNormalizationCover E 1 ⊥) := by
    intro ψ
    obtain ⟨f, hf⟩ := factor_signQuotient hdesc E hj φ ψ
    rw [hrigid E hj0 hj1728 f] at hf
    have hcomp : ψ.comp (Cover.id C) = ψ := Cover.ext_f rfl
    exact hcomp.symm.trans hf
  exact ⟨fun a b => (h a).trans (h b).symm⟩

/-- The complex case from Theorem G and rigidity of the sign quotient. -/
theorem canLift27Complex_of_xDescends_and_hemiRigid
    (hdesc : CanLift27ComplexXDescends) (hrigid : CanLift27ComplexHemiRigid) : CanLift27Complex :=
  canLift27Complex_of_xDescends_and_uniqueCover hdesc
    (canLift27ComplexUniqueCover_of_xDescends_and_hemiRigid hdesc hrigid)

end AbcAdaptation.Reference.Iut.Anabelian
