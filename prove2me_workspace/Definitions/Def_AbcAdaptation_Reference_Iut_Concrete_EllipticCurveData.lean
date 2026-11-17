/-
Adaptation provenance: this wrapper selects original accepted AST command spans.
Original repository: https://github.com/lana-agents/iut
Original commit: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original source: Iut/Concrete/Existence.lean; Iut/Concrete/LocalTheory.lean
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

namespace AbcAdaptation.Reference

namespace Iut

universe u v

open NumberField WeierstrassCurve

/-- An elliptic curve `E` over a number field `F` with a chosen algebraic closure `F̄`. -/
structure EllipticCurveData : Type (u + 1) where
  /-- The number field `F`. -/
  F : Type u
  /-- `F` is a field. -/
  [fieldF : Field F]
  /-- `F` is a number field. -/
  [numberFieldF : NumberField F]
  /-- The algebraic closure `F̄`. -/
  Fbar : Type u
  /-- `F̄` is a field. -/
  [fieldFbar : Field Fbar]
  /-- `F̄` is an `F`-algebra. -/
  [algebraFbar : Algebra F Fbar]
  /-- `F̄` is an algebraic closure of `F`. -/
  [isAlgClosure : IsAlgClosure F Fbar]
  /-- The elliptic curve `E/F`. -/
  E : WeierstrassCurve F
  /-- `E` is an elliptic curve. -/
  [isElliptic : E.IsElliptic]

namespace EllipticCurveData

attribute [instance] fieldF numberFieldF fieldFbar algebraFbar isAlgClosure isElliptic

end EllipticCurveData
end Iut
end AbcAdaptation.Reference
