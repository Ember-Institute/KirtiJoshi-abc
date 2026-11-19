/-
Source: Pi1/Orbicurve/CoreCriterion.lean (`isCoreOf_of_subsingleton`) at revision
ca7def953193f861a462aa0831eec8f0a31ff69f.
Original author: Christian Merten and the pi1 contributors.
License: Apache-2.0.

For an unsigned model of multiplicity one, the relative Galois closure supplies
the common cover used in the range argument.
-/
import Solutions.Source_ReferenceIutCanLiftUnramifiedClosure
import Solutions.Source_ReferenceIutCanLiftCoverDescent

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open Ideal JoshiTeich.Act1Scene1
open JoshiTeich.Act1Scene1.AffineOrbicurvePresentation
open JoshiTeich.Act1Scene1.FunctionFieldNormalization

universe u

variable {k : Type u} [Field k]

private theorem cover_mult_eq_one {V X : AffineOrbicurvePresentation k}
    (φ : Cover V X) (hX : ∀ v : Ideal X.A, v.IsMaximal → X.mult v = 1)
    (w : Ideal V.A) (hw : w.IsMaximal) : V.mult w = 1 := by
  letI : w.IsMaximal := hw
  have hv : (w.comap φ.f).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ φ.isIntegral w
  have hram := φ.ramification w hw
  rw [hX _ hv] at hram
  exact Nat.eq_one_of_mul_eq_one_left hram

private def automorphismCover {V : AffineOrbicurvePresentation k}
    (hV : ∀ w : Ideal V.A, w.IsMaximal → V.mult w = 1) (e : V.A ≃ₐ[k] V.A) : Cover V V where
  f := e.toAlgHom
  injective := e.injective
  isIntegral := RingHom.isIntegral_of_surjective _ e.surjective
  ramification w hw := by
    letI : w.IsMaximal := hw
    letI : w.IsPrime := hw.isPrime
    have hv : (w.comap e.toRingEquiv.toRingHom).IsMaximal :=
      Ideal.comap_isMaximal_of_equiv e.toRingEquiv
    change (letI := e.toRingEquiv.toRingHom.toAlgebra; w.ramificationIdx V.A) * V.mult w =
      V.mult (w.comap e.toRingEquiv.toRingHom)
    rw [ramificationIdx_of_surjective e.toRingEquiv.toRingHom e.surjective w,
      hV w hw, hV _ hv, mul_one]

private theorem comp_mem_range_of_unique_covers [CharZero k]
    {X H Y Z : AffineOrbicurvePresentation k} (π : Cover X H)
    (hX : ∀ v : Ideal X.A, v.IsMaximal → X.mult v = 1)
    (h : ∀ V : AffineOrbicurvePresentation k, Cover V X → Subsingleton (Cover V H))
    (φ : Cover Z X) (ψ : Cover Z Y) (a : H.A) : (φ.comp π).f a ∈ ψ.f.range := by
  obtain ⟨T, γ, G, hG, hact, hgal⟩ := exists_unramified_galoisClosure ψ (cover_mult_eq_one φ hX)
  letI := hG
  letI := hact
  letI : Algebra Y.A T.A := (γ.f.comp ψ.f).toRingHom.toAlgebra
  letI : IsGaloisGroup G Y.A T.A := hgal
  letI : IsScalarTower k Y.A T.A :=
    IsScalarTower.of_algebraMap_eq fun c => ((γ.f.comp ψ.f).commutes c).symm
  let ξ := γ.comp φ
  let θ := ξ.comp π
  have hfixed (g : G) : g • θ.f a = θ.f a := by
    let e : T.A ≃ₐ[Y.A] T.A := MulSemiringAction.toAlgEquiv Y.A T.A g
    let δ := automorphismCover (cover_mult_eq_one ξ hX) (e.restrictScalars k)
    have he := (h T ξ).elim (δ.comp θ) θ
    exact congrArg (fun f : Cover T H => f.f a) he
  obtain ⟨b, hb⟩ := Algebra.IsInvariant.isInvariant (A := Y.A) (G := G) (θ.f a) hfixed
  exact ⟨b, γ.injective hb⟩

/-- If a multiplicity-one presentation has a cover to `H` and every cover of it has at
most one map to `H`, then `H` is its core. -/
theorem isCoreOf_of_unique_covers [CharZero k] {X H : AffineOrbicurvePresentation k}
    (π : Cover X H) (hX : ∀ v : Ideal X.A, v.IsMaximal → X.mult v = 1)
    (h : ∀ Z : AffineOrbicurvePresentation k, Cover Z X → Subsingleton (Cover Z H)) :
    IsCoreOf X H := by
  refine ⟨⟨X, ⟨Cover.id X⟩, ⟨π⟩⟩, ?_⟩
  intro Y hY
  obtain ⟨Z, ⟨φ⟩, ⟨ψ⟩⟩ := hY
  let χ := φ.comp π
  have hrange : ∀ a : H.A, χ.f a ∈ ψ.f.range := comp_mem_range_of_unique_covers π hX h φ ψ
  let e := AlgEquiv.ofInjective ψ.f ψ.injective
  let g := e.symm.toAlgHom.comp (χ.f.codRestrict ψ.f.range hrange)
  have hg : ψ.f.comp g = χ.f := AlgHom.ext fun a =>
    congrArg Subtype.val (e.apply_symm_apply ⟨χ.f a, hrange a⟩)
  refine ⟨⟨Cover.descend ψ χ g hg⟩, ⟨?_⟩⟩
  intro a b
  apply Cover.ext_f
  apply AlgHom.ext
  intro c
  apply ψ.injective
  exact congrArg (fun f : Cover Z H => f.f c) ((h Z φ).elim (ψ.comp a) (ψ.comp b))

end AbcAdaptation.Reference.Iut.Anabelian
