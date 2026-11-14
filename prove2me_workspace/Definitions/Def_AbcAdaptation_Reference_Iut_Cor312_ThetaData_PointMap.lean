/-
Adaptation provenance: this block was inserted by the adaptation; it is not an original source notice.
Original source path: refer/iut/Iut/Cor312/ThetaData/PointMap.lean
Original authors: The iut contributors
Original repository: https://github.com/lana-agents/iut
Original commit: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original license: Apache-2.0; the original copyright and license notice is retained below.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace AbcAdaptation.Reference

/-!
# Points of Weierstrass curves along ring homomorphisms

`Iut.Anabelian.pointMap E f : E(k) →+ (E.map f)(K)` for a ring homomorphism of fields
`f : k →+* K` (Mathlib's `WeierstrassCurve.Affine.Point.map` for the base change `E.map f`),
with its basic properties.
-/

namespace Iut.Anabelian

open WeierstrassCurve

open scoped Classical

/-! ## Points of Weierstrass curves along ring homomorphisms -/

section PointMap

variable {k K L : Type*} [Field k] [Field K] [Field L]

/-- The group homomorphism on points induced by a ring homomorphism of fields
(`WeierstrassCurve.Affine.Point.map` for the base change `E.map f`). -/
noncomputable def pointMap (E : WeierstrassCurve k) (f : k →+* K) :
    E.toAffine.Point →+ (E.map f).toAffine.Point :=
  letI := f.toAlgebra
  Affine.Point.map (W' := E) (S := k) (F := k) (K := K) (Algebra.ofId k K)

variable (E : WeierstrassCurve k) (f : k →+* K)

end PointMap

end Iut.Anabelian

end AbcAdaptation.Reference
