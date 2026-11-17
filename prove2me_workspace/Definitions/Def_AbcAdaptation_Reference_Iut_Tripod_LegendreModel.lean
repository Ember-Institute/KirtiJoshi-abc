/-
Adaptation provenance: original dependency command bytes selected from root-accepted Legendre AST.
Original repository: https://github.com/lana-agents/iut
Original commit: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original source: Iut/Tripod/Legendre.lean
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

namespace AbcAdaptation.Tripod

open WeierstrassCurve

/-- **The Legendre curve** `y² = x³ − (1 + λ)x² + λx = x(x − 1)(x − λ)`. -/
def legendre {R : Type*} [CommRing R] (l : R) : WeierstrassCurve R := ⟨0, -(1 + l), 0, l, 0⟩

end AbcAdaptation.Tripod
