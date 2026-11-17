/-
Mechanical source draft. Original repository: https://github.com/lana-agents/iut
Original snapshot: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license. Authors: The iut contributors
No source theorem statement or proof-body edits. Native correspondence is pending.
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_GlobalField
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_AdmissiblePrime
import Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_QParameter_NormalizedOrder
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Tactic.NormNum

namespace AbcAdaptation.Reference.Iut
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WeierstrassCurve TateCurvesTheta
section Uniformizer
variable {F : Type*} [Field F] [NumberField F] (w : FinitePlace F)

/-- The norm on `F_w` and the valuation `Valued.v` agree on the condition `≤ 1`. -/
lemma norm_le_one_iff_valued (x : localCompletion w) : ‖x‖ ≤ 1 ↔ Valued.v x ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff

/-- The norm on `F_w` and the valuation `Valued.v` agree on the condition `< 1`. -/
lemma norm_lt_one_iff_valued (x : localCompletion w) : ‖x‖ < 1 ↔ Valued.v x < 1 :=
  Valued.toNormedField.norm_lt_one_iff

/-- The norm on `F_w` and the valuation `Valued.v` agree on the condition `= 1`. -/
lemma norm_eq_one_iff_valued (x : localCompletion w) : ‖x‖ = 1 ↔ Valued.v x = 1 := by
  simp only [le_antisymm_iff, norm_le_one_iff_valued, Valued.toNormedField.one_le_norm_iff]

/-- The image in `F_w` of an element of `F` of valuation `exp (-1)` is a uniformizer of the
normed field `F_w`. -/
lemma isUniformizer_of_valuation_eq {π : F}
    (hπ : w.maximalIdeal.valuation F π = WithZero.exp (-1 : ℤ)) :
    IsUniformizer (FinitePlace.embedding w.maximalIdeal π) := by
  have hv : Valued.v (FinitePlace.embedding w.maximalIdeal π) = WithZero.exp (-1 : ℤ) := by
    rw [FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation', hπ]
  have hne : FinitePlace.embedding w.maximalIdeal π ≠ 0 := by
    rw [← (Valued.v).ne_zero_iff, hv]
    exact WithZero.exp_ne_zero
  refine ⟨hne, ?_, ?_⟩
  · rw [norm_lt_one_iff_valued, hv, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  · intro x
    set π' := FinitePlace.embedding w.maximalIdeal π with hπ'
    have hx0 : Valued.v (x : localCompletion w) ≠ 0 := (Valued.v).ne_zero_iff.mpr x.ne_zero
    refine ⟨-WithZero.log (Valued.v (x : localCompletion w)), ?_⟩
    -- the quotient `x / π ^ n` has valuation `1`, hence norm `1`
    have hunit : ‖(x : localCompletion w) / π' ^ (-WithZero.log (Valued.v (x : localCompletion w)))‖
        = 1 := by
      rw [norm_eq_one_iff_valued, map_div₀, map_zpow₀, hv, ← WithZero.exp_zsmul, smul_neg,
        smul_eq_mul, mul_one, neg_neg, WithZero.exp_log hx0, div_self hx0]
    rw [norm_div, norm_zpow] at hunit
    have hπpos : 0 < ‖π'‖ := norm_pos_iff.mpr hne
    have hpow : 0 < ‖π'‖ ^ (-WithZero.log (Valued.v (x : localCompletion w))) := zpow_pos hπpos _
    rw [div_eq_one_iff_eq hpow.ne'] at hunit
    exact hunit

/-- Every completion `F_w` has a uniformizer in the sense of `TateCurvesTheta.IsUniformizer`. -/
lemma exists_isUniformizer : ∃ π : localCompletion w, IsUniformizer π := by
  obtain ⟨π, hπ⟩ := w.maximalIdeal.valuation_exists_uniformizer F
  exact ⟨_, isUniformizer_of_valuation_eq w hπ⟩

end Uniformizer
end AbcAdaptation.Reference.Iut
