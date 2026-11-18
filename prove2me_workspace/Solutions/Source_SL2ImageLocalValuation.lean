/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Concrete/SL2Image.lean (lines 180–213)
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_ModEllRepTorsionField
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_TateFamily
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_TatePoleOrder
import Solutions.Source_TripodRelativeValuation
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  TateCurvesTheta WeierstrassCurve WithZero
open scoped WithZero Valued

universe u

private theorem valued_finitePlaceEmbedding {k : Type*} [Field k] [NumberField k]
    {w : FinitePlace k} (x : k) :
    Valued.v (FinitePlace.embedding w.maximalIdeal x : localCompletion w) =
      w.maximalIdeal.valuation k x := by
  rw [FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation']

private theorem valued_q_eq_inv_tateJ {k : Type*} [Field k] [NumberField k]
    {w : FinitePlace k} (t : TateParameter (localCompletion w)) :
    Valued.v (t.q : localCompletion w) = (Valued.v t.tateJ)⁻¹ := by
  have hnorm : ‖t.tateJ * (t.q : localCompletion w)‖ = 1 := by
    rw [norm_mul, t.norm_tateJ (twelve_ne_zero w),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr t.q.ne_zero)]
  rw [norm_eq_one_iff_valued w, map_mul] at hnorm
  rw [eq_inv_of_mul_eq_one_left hnorm, inv_inv]

namespace EllipticCurveData

/-- The Tate root identity above a multiplicative place gives divisibility of the relative
ramification index if the supplied Tate parameter order at the base place is prime to ℓ. -/
theorem prime_dvd_ramificationIdx_of_root_class (C : EllipticCurveData.{u})
    (TI : C.TateInputs) {ℓ : ℕ} (hℓ : ℓ.Prime) (R : C.ModEllRepData ℓ)
    {w : FinitePlace C.F} (hw : w ∈ C.badAll) (hP2 : ¬ ℓ ∣ TI.qOrder w hw)
    {w' : FinitePlace ↥R.torsionField} (hw'w : FinitePlace.LiesOver w' w)
    (S : TateStructure (curveKw C.E R.torsionField w'))
    (u : (localCompletion w')ˣ) (m : ℤ) (hu : u ^ ℓ = S.t.q ^ (1 + (ℓ : ℤ) * m)) :
    ℓ ∣ w.maximalIdeal.asIdeal.ramificationIdx' w'.maximalIdeal.asIdeal := by
  let e := w.maximalIdeal.asIdeal.ramificationIdx' w'.maximalIdeal.asIdeal
  let n := TI.qOrder w hw
  have hqF : Valued.v ((TI.tate w hw).q : localCompletion w) = exp (-(n : ℤ)) :=
    valued_tateParameter_q _ (TI.unif_isUniformizer w hw)
  have hjF : w.maximalIdeal.valuation C.F C.E.j = exp (n : ℤ) := by
    have h := valued_q_eq_inv_tateJ (TI.tate w hw)
    rw [hqF, TI.tateJ_eq w hw, valued_finitePlaceEmbedding] at h
    rw [← inv_inv (w.maximalIdeal.valuation C.F C.E.j), ← h, ← exp_neg, neg_neg]
  have hJ : S.t.tateJ =
      FinitePlace.embedding w'.maximalIdeal (algebraMap C.F ↥R.torsionField C.E.j) := by
    calc
      S.t.tateJ = (S.C • curveKw C.E R.torsionField w').j := by
        change S.t.tateCurve.c₄ ^ 3 / S.t.tateCurve.Δ = _
        rw [← S.hC, j_eq_inv_Δ_mul, div_eq_inv_mul]
      _ = (curveKw C.E R.torsionField w').j := variableChange_j _ _
      _ = _ := by
        change ((C.E.map (algebraMap C.F ↥R.torsionField)).map
          (FinitePlace.embedding w'.maximalIdeal)).j = _
        rw [map_j, map_j]
  have hqK : Valued.v (S.t.q : localCompletion w') = exp (-((e : ℤ) * n)) := by
    rw [valued_q_eq_inv_tateJ, hJ, valued_finitePlaceEmbedding,
      Tripod.valuation_algebraMap_eq_pow hw'w, hjF, ← exp_nsmul, ← exp_neg, nsmul_eq_mul]
  have hu' := congrArg (fun x : (localCompletion w')ˣ => Valued.v (x : localCompletion w')) hu
  simp only [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, map_pow, map_zpow₀] at hu'
  rw [hqK] at hu'
  have hu0 : Valued.v (u : localCompletion w') ≠ 0 := (Valuation.ne_zero_iff _).mpr u.ne_zero
  rw [← exp_log hu0, ← exp_nsmul, ← exp_zsmul, exp_inj, nsmul_eq_mul, smul_eq_mul] at hu'
  have hdvd : (ℓ : ℤ) ∣ (1 + (ℓ : ℤ) * m) * ((e : ℤ) * n) :=
    ⟨-log (Valued.v (u : localCompletion w')), by linear_combination hu'⟩
  have hmul : (ℓ : ℤ) ∣ ((ℓ : ℤ) * m) * ((e : ℤ) * n) :=
    ⟨m * ((e : ℤ) * n), mul_assoc _ _ _⟩
  rw [add_mul, one_mul, dvd_add_left hmul] at hdvd
  have hdvd' : ℓ ∣ e * n := by exact_mod_cast hdvd
  exact (hℓ.dvd_mul.mp hdvd').resolve_right hP2

end EllipticCurveData
end AbcAdaptation.Reference.Iut
