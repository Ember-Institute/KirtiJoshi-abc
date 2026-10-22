/-
original-path: `refer/iut/.lake/packages/pi1/Pi1/Orbicurve/Core.lean`
original-author: Christian Merten <lana@merten.dev> (Git author; no author header)
original-coauthor: Claude Opus 5.5 (1M context) <noreply@anthropic.com> (Git trailer)
original-commit: `5058425bfd42fa3781314a8bc937e0e3e0f9f6a1`
source-snapshot: `ca7def953193f861a462aa0831eec8f0a31ff69f` (pi1 package)
license: Apache-2.0 (see project `LICENSE`)
license-review: reviewed the package LICENSE before copying. The source has no
copyright header and the package has no NOTICE file. Retain the Apache-2.0 text.
modifications: extract AffOrbicurve and Hom as presentations; rename the etale
field to ramification. Add the actual coarse Spec construction. Do not copy
the core interface or assert a comparison with algebraic stacks.
-/
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the affine coordinate-ring presentation in Pi1/Orbicurve/Core.lean.
fidelity: a Dedekind coordinate ring with positive, finitely supported closed-point
multiplicities, and injective integral maps with the ramification compatibility.
boundary: Scene1/Derived. This is the algebraic presentation used by the reference.
It is not an algebraic-stack construction or an object of an arbitrary AG.Orbicurve.
The root-stack comparison and its etale interpretation remain to be proved.
-/

namespace JoshiTeich.Act1Scene1

universe u

/-- Coordinate-ring and multiplicity data for an affine orbicurve presentation. -/
structure AffineOrbicurvePresentation (k : Type u) [Field k] : Type (u + 1) where
  A : Type u
  [commRing : CommRing A]
  [isDomain : IsDomain A]
  [algebra : Algebra k A]
  [isDedekindDomain : IsDedekindDomain A]
  [finiteType : Algebra.FiniteType k A]
  not_isField : ¬ IsField A
  mult : Ideal A → ℕ
  mult_pos : ∀ v : Ideal A, v.IsMaximal → 0 < mult v
  finite_mult : {v : Ideal A | v.IsMaximal ∧ mult v ≠ 1}.Finite

namespace AffineOrbicurvePresentation

attribute [instance] commRing isDomain algebra isDedekindDomain finiteType

variable {k : Type u} [Field k]

/-- An integral inclusion with the closed-point ramification compatibility. -/
structure Cover (Y C : AffineOrbicurvePresentation k) where
  f : C.A →ₐ[k] Y.A
  injective : Function.Injective f
  isIntegral : f.toRingHom.IsIntegral
  ramification : ∀ w : Ideal Y.A, w.IsMaximal →
    (letI := f.toRingHom.toAlgebra; w.ramificationIdx C.A) * Y.mult w = C.mult (w.comap f)

/-- The actual affine scheme of the presentation's coordinate ring. -/
noncomputable def coarseScheme (X : AffineOrbicurvePresentation k) : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (CommRingCat.of X.A)

/-- The scheme map induced by the presentation's coordinate-ring map. -/
noncomputable def Cover.coarseMap {Y C : AffineOrbicurvePresentation k} (φ : Cover Y C) :
    Y.coarseScheme ⟶ C.coarseScheme :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ.f.toRingHom)

end AffineOrbicurvePresentation
end JoshiTeich.Act1Scene1
