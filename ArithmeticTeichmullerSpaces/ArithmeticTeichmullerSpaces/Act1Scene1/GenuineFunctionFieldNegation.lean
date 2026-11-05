/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.WeierstrassCoordinateNegation
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Genuine.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
source-id: JT-SCENE1-GENUINE-FUNCTION-FIELD-NEGATION
source: IUT I Definition 3.1(d), the signed quotient of the punctured elliptic
curve; Mathlib `IsFractionRing.algEquivOfAlgEquiv` and `div_surjective` in
`RingTheory/Localization/FractionRing.lean`.
fidelity: extends the proved coordinate-ring involution to the original
`E.toAffine.FunctionField`, fixes its polynomial x-coordinate algebra, and
proves the formulas for the pre-existing `xF` and `yF`, with involutivity.
This is an independent proof using the existing local coordinate definitions.
boundary: Scene1/Derived. It does not construct an automorphism of `Ω E`,
prove signed-quotient nontriviality or the Cartesian normalization square.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

universe u
open WeierstrassCurve Polynomial
open JoshiTeich.Act1Scene1.WeierstrassCoordinateNegation
noncomputable section

variable {k : Type u} [Field k] (E : WeierstrassCurve k)

/-- Negation on the original Weierstrass function field. -/
def functionFieldNegationEquiv : E.toAffine.FunctionField ≃ₐ[k] E.toAffine.FunctionField :=
  IsFractionRing.algEquivOfAlgEquiv ((coordinateNegationEquiv E).restrictScalars k)

/-- The fraction-field map restricts to the original coordinate-ring involution. -/
@[simp] theorem functionFieldNegationEquiv_algebraMap (a : E.toAffine.CoordinateRing) :
    functionFieldNegationEquiv E (algebraMap _ E.toAffine.FunctionField a) =
      algebraMap _ E.toAffine.FunctionField (coordinateNegationEquiv E a) := by
  exact IsFractionRing.algEquivOfAlgEquiv_algebraMap
    ((coordinateNegationEquiv E).restrictScalars k) a

/-- Negation fixes the whole original polynomial x-coordinate algebra. -/
@[simp] theorem functionFieldNegationEquiv_polynomial (p : k[X]) :
    functionFieldNegationEquiv E
        (algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField
          (algebraMap k[X] E.toAffine.CoordinateRing p)) =
      algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField
        (algebraMap k[X] E.toAffine.CoordinateRing p) := by
  rw [functionFieldNegationEquiv_algebraMap, coordinateNegationEquiv_algebraMap]

/-- The pre-existing generic x-coordinate is fixed. -/
@[simp] theorem functionFieldNegationEquiv_xF :
    functionFieldNegationEquiv E (xF E) = xF E := by
  exact functionFieldNegationEquiv_polynomial E X

/-- The pre-existing generic y-coordinate has the affine negation formula. -/
@[simp] theorem functionFieldNegationEquiv_yF :
    functionFieldNegationEquiv E (yF E) =
      -yF E - algebraMap k E.toAffine.FunctionField E.a₁ * xF E -
        algebraMap k E.toAffine.FunctionField E.a₃ := by
  have hc (c : k) :
      algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField
          (algebraMap k[X] E.toAffine.CoordinateRing (C c)) =
        algebraMap k E.toAffine.FunctionField c := by
    rw [Polynomial.C_eq_algebraMap,
      ← IsScalarTower.algebraMap_apply k k[X] E.toAffine.CoordinateRing,
      ← IsScalarTower.algebraMap_apply k E.toAffine.CoordinateRing E.toAffine.FunctionField]
  change functionFieldNegationEquiv E
      (algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField
        (AdjoinRoot.root E.toAffine.polynomial)) = _
  rw [functionFieldNegationEquiv_algebraMap, coordinateNegationEquiv_root]
  simp only [map_sub, map_neg, map_add, map_mul]
  rw [hc E.a₁, hc E.a₃]
  change -yF E - (algebraMap k E.toAffine.FunctionField E.a₁ * xF E +
    algebraMap k E.toAffine.FunctionField E.a₃) = _
  abel

/-- The original function-field involution squares to the identity. -/
theorem functionFieldNegationEquiv_involutive :
    Function.Involutive (functionFieldNegationEquiv E) := by
  intro z
  obtain ⟨a, b, _, rfl⟩ :=
    IsFractionRing.div_surjective (A := E.toAffine.CoordinateRing) z
  simp only [map_div₀, functionFieldNegationEquiv_algebraMap,
    coordinateNegationEquiv_apply_apply]

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
