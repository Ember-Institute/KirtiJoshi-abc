/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Authors: The iut contributors
-/
/-
Uncompiled draft: source declaration bodies selected byte-for-byte; wrappers and imports adapted.
Original repository: https://github.com/lana-agents/iut
Original revision recorded by existing adaptation: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
This draft does not itself establish accepted AST-command provenance.
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_EllipticCurveData
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

namespace AbcAdaptation.Reference.Iut
open NumberField
section Tripodal
variable (F : Type*) [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]

open scoped Classical in
/-- The `x`-coordinates of the `F`-rational `2`-torsion points of `E`. -/
def twoTorsionXOf : Set F :=
  {a | ∃ (b : F) (h : E.toAffine.Nonsingular a b),
    WeierstrassCurve.Affine.Point.some a b h ∈ AddSubgroup.torsionBy E.toAffine.Point 2}

/-- **The tripodal field** `F_tpd = F_mod(E[2])` (IUT IV, Theorem 1.10; Proposition
1.8(ii),(iii)): the subfield of `F` generated over `ℚ` by `j(E)` and the `x`-coordinates
of the `2`-torsion points (rational over `F` by IUT I, Definition 3.1(b)). -/
noncomputable def tripodalFieldOf : IntermediateField ℚ F :=
  IntermediateField.adjoin ℚ (insert E.j (twoTorsionXOf F E))

instance : FiniteDimensional ℚ ↥(tripodalFieldOf F E) :=
  Module.Finite.left ℚ ↥(tripodalFieldOf F E) F

instance : NumberField ↥(tripodalFieldOf F E) where

end Tripodal
end AbcAdaptation.Reference.Iut
