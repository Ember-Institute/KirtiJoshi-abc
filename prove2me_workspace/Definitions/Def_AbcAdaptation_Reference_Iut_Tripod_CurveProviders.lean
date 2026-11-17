/-
Adaptation provenance: accepted exact Iut AST command selection; no source-body rewrite.
Original repository: https://github.com/lana-agents/iut
Original commit: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original sources: Iut/Concrete/Existence.lean; Iut/Tripod/CurveFacts.lean;
Iut/Cor312/ThetaData/Places.lean; Iut/Concrete/TateInputsConstruct.lean
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveOf
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_CurveData

namespace AbcAdaptation.Tripod
open AbcAdaptation.Reference.Iut
open WeierstrassCurve NumberField Polynomial
open scoped IntermediateField

/-- **The providers of the curve data**: the finiteness of the `3`- and `5`-torsion of
`E_λ(ℚ̄)` for every `λ`, the arithmetic `EllipticCurveData.CurveArithmetic` of `E_λ/F_λ`
(IUT IV, Proposition 1.8: everywhere stable reduction, `F_λ/F_mod` Galois of degree prime
to `ℓ ≥ 7`, …; its fields `sqrt_neg_one` and `six_torsion_rational` are proved above and
the five general fields in `Iut.EllipticCurveData.CurveArithmetic.ofCore`), and the
mod-`ℓ` representations (`Iut.EllipticCurveData.modEllRepData` from a basis of
`E_λ[ℓ]`). -/
structure CurveProviders where
  /-- The `3`-torsion of `E_λ(ℚ̄)` is finite. -/
  torsionFinite3 : ∀ l : Qbar, TorsionFinite l 3
  /-- The `5`-torsion of `E_λ(ℚ̄)` is finite. -/
  torsionFinite5 : ∀ l : Qbar, TorsionFinite l 5
  /-- The arithmetic of `E_λ/F_λ`. -/
  arith : ∀ x : Pt, (curveOf x (torsionFinite3 x.1) (torsionFinite5 x.1)).CurveArithmetic
  /-- The mod-`ℓ` representations of `E_λ`. -/
  modRep : ∀ (x : Pt) (ℓ : ℕ), ℓ.Prime →
    (curveOf x (torsionFinite3 x.1) (torsionFinite5 x.1)).ModEllRepData ℓ

namespace CurveProviders
variable (P : CurveProviders)

/-- The curve `E_λ/F_λ` of a point. -/
noncomputable def curve (x : Pt) : EllipticCurveData :=
  curveOf x (P.torsionFinite3 x.1) (P.torsionFinite5 x.1)

end CurveProviders
end AbcAdaptation.Tripod
