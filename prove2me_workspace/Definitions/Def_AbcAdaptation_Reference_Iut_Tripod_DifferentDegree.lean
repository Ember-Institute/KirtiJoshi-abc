/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original revision: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths: Iut/Tripod/CurveFacts.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_DmodBound
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField
open scoped IntermediateField

/-- `log(d_L)` is invariant under `ℚ`-isomorphisms of number fields. -/
theorem logDifferentDeg_eq_of_algEquiv {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] (f : K ≃ₐ[ℚ] L) : logDifferentDeg K = logDifferentDeg L := by
  unfold logDifferentDeg
  rw [absNorm_differentIdeal (K := K), absNorm_differentIdeal (K := L),
    discr_eq_discr_of_algEquiv K f, f.toLinearEquiv.finrank_eq]

/-- `log-diff_ℙ(λ) = log(d_{ℚ(λ)})`. -/
theorem logDiff_eq_logDifferentDeg (x : Pt) : logDiff x = logDifferentDeg (fieldOf x.1) := by
  rw [logDiff_eq_log_absNorm_differentIdeal, logDifferentDeg, deg_eq_finrank]

variable (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5)

/-- **`log-diff_ℙ(λ)` is the different degree of the tripodal field** `F_tpd = ℚ(λ)`. -/
theorem logDiff_eq :
    logDiff x = logDifferentDeg ↥(tripodalFieldOf (curveOf x h3 h5).F (curveOf x h3 h5).E) := by
  haveI : FiniteDimensional ℚ ℚ⟮genC x h3 h5⟯ :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_genC x h3 h5)
  rw [logDiff_eq_logDifferentDeg]
  exact (logDifferentDeg_eq_of_algEquiv
    ((IntermediateField.equivOfEq (tripodalFieldOf_eq x h3 h5)).trans
      (adjoinGenCEquiv x h3 h5))).symm

end AbcAdaptation.Tripod
