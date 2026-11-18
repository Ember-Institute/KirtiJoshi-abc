/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original revision: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths: Iut/Concrete/Invariants.lean and Iut/Concrete/Existence.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FieldInvariant
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_GlobalField
import Mathlib.NumberTheory.NumberField.Discriminant.Different

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

universe u

open NumberField WeierstrassCurve

/-- The normalized degree `log(d_L) = log N(𝔡_{L/ℚ})/[L : ℚ]` of the different divisor of a
number field `L` (IUT IV, Theorem 1.10: `deg(d_ADiv)`). -/
noncomputable def logDifferentDeg (L : Type*) [Field L] [NumberField L] : ℝ :=
  Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 L))) / Module.finrank ℚ L

section Tripodal

variable (F : Type*) [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]

variable (VBad : Set (FinitePlace ↥(fieldOfModuli F E)))

/-- A finite place of `F_tpd` is **bad** if a bad place of `F` lies over it. -/
def IsBadTpdOf (𝔭 : FinitePlace ↥(tripodalFieldOf F E)) : Prop :=
  ∃ w ∈ badPlacesOver F E VBad, FinitePlace.LiesOver w 𝔭

open scoped Classical in
/-- The normalized degree `log(f_{F_tpd})` of the **conductor divisor** of `F_tpd`: the
sum of `log N(𝔭)` over the bad places of `F_tpd`, divided by `[F_tpd : ℚ]` (finitely
supported; `0` if not). -/
noncomputable def logConductorDegOf : ℝ :=
  (∑ᶠ 𝔭 : FinitePlace ↥(tripodalFieldOf F E),
    if IsBadTpdOf F E VBad 𝔭 then Real.log (Ideal.absNorm 𝔭.maximalIdeal.asIdeal) else 0) /
    Module.finrank ℚ ↥(tripodalFieldOf F E)

end Tripodal

namespace EllipticCurveData

variable (C : EllipticCurveData.{u})

/-- The set `V_mod^bad` attached to the prime `ℓ` ((P5) in the proof of IUT IV,
Corollary 2.2): the places of `F_mod` of residue characteristic `≠ 2, ℓ` over which `E`
has multiplicative reduction (at every place of `F` above, and there is one). -/
def VBadOf (ℓ : ℕ) : Set (FinitePlace ↥(fieldOfModuli C.F C.E)) :=
  {v | residueChar v ≠ 2 ∧ residueChar v ≠ ℓ ∧
    (∃ w : FinitePlace C.F, FinitePlace.LiesOver w v) ∧
    ∀ w : FinitePlace C.F, FinitePlace.LiesOver w v → HasMultiplicativeReductionAt C.E w}

end EllipticCurveData
end AbcAdaptation.Reference.Iut
