import Solutions.Source_ReferenceIutCanLiftComplex
import Mathlib.RingTheory.IsGaloisGroup.Defs

/-!
The fixed-ring step of Theorem G from `OrbicurveCores/U2/CoreMap.lean` at revision
61616dcd77fbe45c083a8ebfa7cc80728f86e841. The inputs are the unramifiedness of the
Galois closure from `U2/GaloisClosure.lean` and invariance under automorphisms from
`U2/TheoremG.lean`.
-/

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open WeierstrassCurve JoshiTeich.Act1Scene1
open JoshiTeich.Act1Scene1.AffineOrbicurvePresentation
open JoshiTeich.ReferenceIut.Anabelian.Genuine

/-- The analytic part of Theorem G on an affine normalization of a once-punctured elliptic
curve. Every automorphism of a finite étale cover of the curve fixes the pulled-back `x`. -/
def CanLift27ComplexAutomorphismsFixX : Prop :=
  ∀ (E : WeierstrassCurve ℂ) [E.IsElliptic], (∀ c ∈ canLiftExceptionalJ, E.j ≠ (c : ℂ)) →
    ∀ {T : AffineOrbicurvePresentation ℂ}
      (π : Cover T (normalizationPresentation E 1 ⊥ false)) (σ : T.A ≃ₐ[ℂ] T.A),
        σ (π.f (normalizationBaseX E)) = π.f (normalizationBaseX E)

/-- When the source of an orbicurve cover has multiplicity one, its Galois closure over the
target can be represented by a further cover of the source with the target as fixed ring. -/
def CanLift27UnramifiedGaloisClosure : Prop :=
  ∀ {Z Y : AffineOrbicurvePresentation ℂ} (ψ : Cover Z Y),
    (∀ w : Ideal Z.A, w.IsMaximal → Z.mult w = 1) →
    ∃ (T : AffineOrbicurvePresentation ℂ) (γ : Cover T Z) (G : Type) (hG : Group G),
      letI := hG
      ∃ hact : MulSemiringAction G T.A,
        letI := hact
        letI := (γ.f.comp ψ.f).toRingHom.toAlgebra
        IsGaloisGroup G Y.A T.A

/-- Automorphism invariance on the Galois closure gives Theorem G on the given common
cover, with the descended element in the actual target coordinate ring. -/
theorem canLift27ComplexXDescends_of_automorphisms
    (hfix : CanLift27ComplexAutomorphismsFixX) (hclosure : CanLift27UnramifiedGaloisClosure) :
    CanLift27ComplexXDescends := by
  intro E _ hj Y Z φ ψ
  have hmult (w : Ideal Z.A) (hw : w.IsMaximal) : Z.mult w = 1 :=
    Nat.eq_one_of_mul_eq_one_left (φ.ramification w hw)
  obtain ⟨T, γ, G, hG, hact, hgal⟩ := hclosure ψ hmult
  letI := hG
  letI := hact
  letI : Algebra Y.A T.A := (γ.f.comp ψ.f).toRingHom.toAlgebra
  letI : IsGaloisGroup G Y.A T.A := hgal
  letI : IsScalarTower ℂ Y.A T.A :=
    IsScalarTower.of_algebraMap_eq fun a => ((γ.f.comp ψ.f).commutes a).symm
  let π := γ.comp φ
  let x := π.f (normalizationBaseX E)
  have hx (g : G) : g • x = x := by
    let σ : T.A ≃ₐ[Y.A] T.A := MulSemiringAction.toAlgEquiv Y.A T.A g
    exact hfix E hj π (σ.restrictScalars ℂ)
  obtain ⟨y, hy⟩ := Algebra.IsInvariant.isInvariant (A := Y.A) (G := G) x hx
  exact ⟨y, γ.injective hy⟩

end AbcAdaptation.Reference.Iut.Anabelian
