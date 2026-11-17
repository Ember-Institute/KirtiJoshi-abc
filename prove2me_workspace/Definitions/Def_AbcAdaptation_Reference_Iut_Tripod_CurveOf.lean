/-
Adaptation provenance: exact accepted Iut AST command spans.
Original repository: https://github.com/lana-agents/iut
Original commit: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original source: Iut/Tripod/CurveOf.lean
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveOfCarrier
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_EllipticCurveData
import Theorems.Thm_AbcAdaptation_Tripod_finiteDimensional_fieldOfExtended

namespace AbcAdaptation.Tripod
open WeierstrassCurve NumberField
open scoped IntermediateField

open AbcAdaptation.Reference.Iut

/-- **The elliptic curve of a point `λ` of the tripod**: the Legendre curve `E_λ` over its
field of definition `F_λ = ℚ(λ, √−1, √λ, √(1 − λ), E_λ[3], E_λ[5])`, with the algebraic
closure `ℚ̄`. -/
noncomputable def curveOf (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5) :
    EllipticCurveData :=
  letI := finiteDimensional_fieldOfExtended h3 h5
  { F := fieldOf' x.1
    Fbar := Qbar
    E := legendre (gen' x.1)
    isElliptic := legendre_gen'_isElliptic x }

end AbcAdaptation.Tripod
