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
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_CurveData
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_PrimeSelection

namespace AbcAdaptation.Reference.Iut
universe u v
open NumberField IsDedekindDomain WeierstrassCurve TateCurvesTheta
section ResidueCharacteristic
variable {k : Type*} [Field k] [NumberField k]

/-- The residue characteristic of a finite place of a number field is prime. -/
lemma residueChar_prime (w : FinitePlace k) : (residueChar w).Prime := by
  haveI : w.maximalIdeal.asIdeal.IsMaximal :=
    w.maximalIdeal.isPrime.isMaximal w.maximalIdeal.ne_bot
  letI : Field (𝓞 k ⧸ w.maximalIdeal.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 k ⧸ w.maximalIdeal.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ w.maximalIdeal.ne_bot
  exact CharP.char_is_prime (𝓞 k ⧸ w.maximalIdeal.asIdeal) (ringChar _)

end ResidueCharacteristic
namespace EllipticCurveData
variable (C : EllipticCurveData.{u})

open scoped Classical in
/-- **The local height data** of `E/F` (IUT IV, Theorem 1.10; [GenEll], Definition 3.3):
the multiplicative places with their residue characteristics, the orders of the Tate
parameters, and the residue degrees. -/
noncomputable def localHeightData (CA : C.CurveArithmetic) (TI : C.TateInputs) :
    LocalHeightData.{u} where
  ι := FinitePlace C.F
  bad := CA.badAll_finite.toFinset
  p := residueChar
  hv w := if h : w ∈ C.badAll then TI.qOrder w h else 0
  f := inertDeg C.F
  deg := Module.finrank ℚ C.F
  one_le_deg := Module.finrank_pos
  p_prime w _ := residueChar_prime w
  one_le_hv w hw := by
    rw [Set.Finite.mem_toFinset] at hw
    rw [dif_pos hw]
    exact TI.qOrder_pos w hw
  one_le_f w _ := CA.inertDeg_pos w
  sum_f_le := CA.sum_inertDeg_le

end EllipticCurveData
end AbcAdaptation.Reference.Iut
