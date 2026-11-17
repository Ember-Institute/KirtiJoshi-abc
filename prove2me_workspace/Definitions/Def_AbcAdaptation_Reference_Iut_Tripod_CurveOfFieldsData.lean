/-
Adaptation provenance: accepted source AST command selection, original declaration bytes unchanged.
Original repository: https://github.com/lana-agents/iut
Original commit: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original source: Iut/Tripod/CurveOf.lean
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Definitions.Def_AbcTripod
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_LegendreModel
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

namespace AbcAdaptation.Tripod

open WeierstrassCurve NumberField

open scoped IntermediateField

/-- A chosen square root of `−1` in `ℚ̄`. -/
noncomputable def sqrtNegOne : Qbar :=
  (IsAlgClosed.exists_pow_nat_eq (-1 : Qbar) two_pos).choose

/-- A chosen square root of `λ` in `ℚ̄`. -/
noncomputable def sqrtLam (l : Qbar) : Qbar := (IsAlgClosed.exists_pow_nat_eq l two_pos).choose

/-- A chosen square root of `1 − λ` in `ℚ̄`. -/
noncomputable def sqrtOneSubLam (l : Qbar) : Qbar :=
  (IsAlgClosed.exists_pow_nat_eq (1 - l) two_pos).choose

/-- The set of affine coordinates of a point of `E_λ(ℚ̄)`: `∅` for the origin, `{x, y}` for an
affine point `(x, y)`. -/
def coords {l : Qbar} : (legendre l).toAffine.Point → Set Qbar
  | 0 => ∅
  | Affine.Point.some x y _ => {x, y}

open scoped Classical in
/-- The `n`-torsion points of `E_λ(ℚ̄)`. -/
def torsionSet (l : Qbar) (n : ℕ) : Set (legendre l).toAffine.Point := {P | n • P = 0}

/-- **Finiteness of the `n`-torsion** of `E_λ(ℚ̄)`: the hypothesis of the construction of
the field of definition. It is a theorem for every `λ` and `n ≠ 0`
(`Iut.Tripod.legendre_torsionFinite`, from the division polynomials), and follows also from
`E_λ[n](ℚ̄) ≅ (ℤ/n)²` (`torsionFinite_of_equiv`). -/
def TorsionFinite (l : Qbar) (n : ℕ) : Prop := (torsionSet l n).Finite

/-- The coordinates of the `n`-torsion points of `E_λ(ℚ̄)`. -/
def torsionCoords (l : Qbar) (n : ℕ) : Set Qbar := ⋃ P ∈ torsionSet l n, coords P

/-- **The field of definition** `F_λ = ℚ(λ, √−1, √λ, √(1 − λ), E_λ[3], E_λ[5]) ⊆ ℚ̄` of the
Legendre curve of `λ`.

The square roots `√λ`, `√(1 − λ)` are adjoined so that `F_λ` is Galois over the field of
moduli `ℚ(j)`, as required by `Iut.IsGaloisOfDegreePrimeTo` (proved in
`Iut/Tripod/Galois.lean`): over `ℚ(j)` the conjugates of `λ` are the six values
`λ, 1 − λ, 1/λ, 1/(1 − λ), λ/(λ − 1), (λ − 1)/λ`; `E_{1−λ} ≅ E_λ` over `ℚ(λ, √−1)`, while
`E_{1/λ}` and `E_{1/(1−λ)}` are the quadratic twists of `E_λ` by `λ` and by `1 − λ`, so
`ℚ(λ, √−1, √λ, √(1 − λ), E_λ[15])` contains the `15`-torsion fields of all the conjugate
curves and is Galois over `ℚ(j)`. -/
noncomputable def fieldOf' (l : Qbar) : IntermediateField ℚ Qbar :=
  IntermediateField.adjoin ℚ
    ({l, sqrtNegOne, sqrtLam l, sqrtOneSubLam l} ∪ torsionCoords l 3 ∪ torsionCoords l 5)

end AbcAdaptation.Tripod
