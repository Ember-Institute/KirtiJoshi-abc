/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.Abel

/-!
source-id: JT-SCENE1-WEIERSTRASS-COORDINATE-NEGATION
source: IUT I Definition 3.1(d), the signed quotient of a punctured elliptic
curve; Mathlib `WeierstrassCurve.Affine.negPolynomial` and
`WeierstrassCurve.Affine.negY` in
`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean`.
fidelity: constructs the involution on the original Weierstrass coordinate
ring as a `k[X]`-algebra automorphism. It fixes the polynomial x-coordinate
and maps the original y-coordinate to `-y-a₁x-a₃`.
boundary: Scene1/Derived. This module does not extend the map
to a function field, construct an ambient algebraic-closure automorphism,
or prove the Cartesian normalization square.

Pinned API locations:
* `Mathlib/RingTheory/AdjoinRoot.lean`: `eval₂_root` (line 255),
  `liftAlgHom` (line 317), `liftAlgHom_of` (line 328),
  `liftAlgHom_root` (line 336), and `algHom_ext` (line 203).
* `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean`:
  `Affine.polynomial`, the original monic quadratic relation.
* `Mathlib/Algebra/Algebra/Equiv.lean`: `AlgEquiv.ofBijective` (line 576).

The accepted leaf build uses the default heartbeat under the Scene1 controlled
build rules. The proof only requires a commutative coefficient ring; no
ellipticity, characteristic or field hypothesis is used.
-/

namespace JoshiTeich.Act1Scene1.WeierstrassCoordinateNegation

universe u
open WeierstrassCurve Polynomial
noncomputable section

variable {k : Type u} [CommRing k] (E : WeierstrassCurve k)

private theorem coordinateRing_algebraMap_C (a : k) :
    algebraMap k[X] E.toAffine.CoordinateRing (C a) =
      algebraMap k E.toAffine.CoordinateRing a := by
  rw [IsScalarTower.algebraMap_apply k k[X] E.toAffine.CoordinateRing,
    AdjoinRoot.algebraMap_eq, ← Polynomial.C_eq_algebraMap]

/-- Evaluation of the outer polynomial using the original x generator. -/
private theorem xGeneratorEval₂RingHom_eq :
    eval₂RingHom (algebraMap k E.toAffine.CoordinateRing)
        (algebraMap k[X] E.toAffine.CoordinateRing X) =
      algebraMap k[X] E.toAffine.CoordinateRing := by
  apply Polynomial.ringHom_ext
  · intro a
    simpa only [← RingHom.comp_apply, eval₂RingHom_comp_C] using
      (coordinateRing_algebraMap_C E a).symm
  · simp

/-- The original y generator satisfies the affine Weierstrass equation. -/
private theorem coordinateRingRoot_equation :
    (E.toAffine.map (algebraMap k E.toAffine.CoordinateRing)).Equation
      (algebraMap k[X] E.toAffine.CoordinateRing X)
      (AdjoinRoot.root E.toAffine.polynomial) := by
  change (E.toAffine.map (algebraMap k E.toAffine.CoordinateRing)).polynomial.evalEval
    (algebraMap k[X] E.toAffine.CoordinateRing X)
    (AdjoinRoot.root E.toAffine.polynomial) = 0
  rw [Affine.map_polynomial,
    ← eval₂_eval₂RingHom_apply (algebraMap k E.toAffine.CoordinateRing)
      (algebraMap k[X] E.toAffine.CoordinateRing X)
      (AdjoinRoot.root E.toAffine.polynomial) E.toAffine.polynomial,
    xGeneratorEval₂RingHom_eq]
  exact AdjoinRoot.eval₂_root E.toAffine.polynomial

/-- The original y generator satisfies the same quadratic relation after negation. -/
private theorem negationRoot_isRoot :
    E.toAffine.polynomial.eval₂
      (algebraMap k[X] E.toAffine.CoordinateRing)
      (-AdjoinRoot.root E.toAffine.polynomial -
        algebraMap k[X] E.toAffine.CoordinateRing (C E.a₁ * X + C E.a₃)) = 0 := by
  let f : k →+* E.toAffine.CoordinateRing := algebraMap k E.toAffine.CoordinateRing
  let W := E.toAffine.map f
  let x : E.toAffine.CoordinateRing := algebraMap k[X] E.toAffine.CoordinateRing X
  let y : E.toAffine.CoordinateRing := AdjoinRoot.root E.toAffine.polynomial
  have hneg : W.Equation x (W.negY x y) := (W.equation_neg x y).mpr
    (coordinateRingRoot_equation E)
  have hy : W.negY x y =
      -AdjoinRoot.root E.toAffine.polynomial -
        algebraMap k[X] E.toAffine.CoordinateRing (C E.a₁ * X + C E.a₃) := by
    rw [show W.negY x y = -y - f E.a₁ * x - f E.a₃ by
      simp [W, Affine.negY, f]]
    rw [← coordinateRing_algebraMap_C E E.a₁,
      ← coordinateRing_algebraMap_C E E.a₃]
    dsimp [x, y]
    rw [map_add]
    have hmul : (AdjoinRoot.of E.toAffine.polynomial) (C E.a₁ * X) =
        (AdjoinRoot.of E.toAffine.polynomial) (C E.a₁) *
          (AdjoinRoot.of E.toAffine.polynomial) X := by
      exact map_mul (AdjoinRoot.of E.toAffine.polynomial) (C E.a₁) X
    rw [hmul]
    abel
  rw [hy] at hneg
  change W.polynomial.evalEval x
    (-AdjoinRoot.root E.toAffine.polynomial -
      algebraMap k[X] E.toAffine.CoordinateRing (C E.a₁ * X + C E.a₃)) = 0 at hneg
  rw [Affine.map_polynomial] at hneg
  rw [← eval₂_eval₂RingHom_apply f x
    (-AdjoinRoot.root E.toAffine.polynomial -
      algebraMap k[X] E.toAffine.CoordinateRing (C E.a₁ * X + C E.a₃))
    E.toAffine.polynomial] at hneg
  rw [xGeneratorEval₂RingHom_eq] at hneg
  exact hneg

/-- Negation fixes the whole polynomial x-coordinate algebra. -/
def coordinateNegationHom :
    E.toAffine.CoordinateRing →ₐ[k[X]] E.toAffine.CoordinateRing :=
  AdjoinRoot.liftAlgHom E.toAffine.polynomial
    (Algebra.ofId k[X] E.toAffine.CoordinateRing)
    (-AdjoinRoot.root E.toAffine.polynomial -
      algebraMap k[X] E.toAffine.CoordinateRing (C E.a₁ * X + C E.a₃))
    (negationRoot_isRoot E)

@[simp] theorem coordinateNegationHom_root :
    coordinateNegationHom E (AdjoinRoot.root E.toAffine.polynomial) =
      -AdjoinRoot.root E.toAffine.polynomial -
        algebraMap k[X] E.toAffine.CoordinateRing (C E.a₁ * X + C E.a₃) := by
  simpa only [coordinateNegationHom] using
    (AdjoinRoot.liftAlgHom_root (p := E.toAffine.polynomial)
      (i := Algebra.ofId k[X] E.toAffine.CoordinateRing)
      (x := -AdjoinRoot.root E.toAffine.polynomial -
        algebraMap k[X] E.toAffine.CoordinateRing (C E.a₁ * X + C E.a₃))
      (h := negationRoot_isRoot E))

@[simp] theorem coordinateNegationHom_algebraMap (p : k[X]) :
    coordinateNegationHom E (algebraMap k[X] E.toAffine.CoordinateRing p) =
      algebraMap k[X] E.toAffine.CoordinateRing p :=
  (coordinateNegationHom E).commutes p

/-- Two applications give the identity on the original coordinate ring. -/
theorem coordinateNegationHom_involutive :
    Function.Involutive (coordinateNegationHom E) := by
  have hcomp : (coordinateNegationHom E).comp (coordinateNegationHom E) =
      AlgHom.id k[X] E.toAffine.CoordinateRing := by
    apply AdjoinRoot.algHom_ext
    simp only [AlgHom.comp_apply, AlgHom.id_apply, coordinateNegationHom_root,
      map_sub, map_neg, coordinateNegationHom_algebraMap]
    abel
  intro a
  change ((coordinateNegationHom E).comp (coordinateNegationHom E)) a =
    (AlgHom.id k[X] E.toAffine.CoordinateRing) a
  rw [hcomp]

/-- The signed-quotient involution of the original Weierstrass coordinate ring. -/
def coordinateNegationEquiv :
    E.toAffine.CoordinateRing ≃ₐ[k[X]] E.toAffine.CoordinateRing :=
  AlgEquiv.ofBijective (coordinateNegationHom E)
    ⟨(coordinateNegationHom_involutive E).injective,
      (coordinateNegationHom_involutive E).surjective⟩

@[simp] theorem coordinateNegationEquiv_apply (a : E.toAffine.CoordinateRing) :
    coordinateNegationEquiv E a = coordinateNegationHom E a := rfl

@[simp] theorem coordinateNegationEquiv_root :
    coordinateNegationEquiv E (AdjoinRoot.root E.toAffine.polynomial) =
      -AdjoinRoot.root E.toAffine.polynomial -
        algebraMap k[X] E.toAffine.CoordinateRing (C E.a₁ * X + C E.a₃) :=
  coordinateNegationHom_root E

@[simp] theorem coordinateNegationEquiv_algebraMap (p : k[X]) :
    coordinateNegationEquiv E (algebraMap k[X] E.toAffine.CoordinateRing p) =
      algebraMap k[X] E.toAffine.CoordinateRing p :=
  coordinateNegationHom_algebraMap E p

@[simp] theorem coordinateNegationEquiv_apply_apply (a : E.toAffine.CoordinateRing) :
    coordinateNegationEquiv E (coordinateNegationEquiv E a) = a :=
  coordinateNegationHom_involutive E a

end
end JoshiTeich.Act1Scene1.WeierstrassCoordinateNegation
