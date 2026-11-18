/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviderHeight

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WeierstrassCurve

section Local
variable {F : Type*} [Field F] [NumberField F] (w : FinitePlace F)

/-- Elements of the completed integers have norm at most one. -/
lemma norm_algebraMap_le_one (r : w.maximalIdeal.adicCompletionIntegers F) :
    ‖algebraMap (w.maximalIdeal.adicCompletionIntegers F) (localCompletion w) r‖ ≤ 1 :=
  (norm_le_one_iff_valued w _).2 r.2

end Local

section Integral
variable {F : Type*} [Field F] [NumberField F] {w : FinitePlace F}
  (W : WeierstrassCurve (localCompletion w))
variable [W.IsIntegral (w.maximalIdeal.adicCompletionIntegers F)]

lemma norm_c₄_le_one : ‖W.c₄‖ ≤ 1 := by
  rw [← integralModel_c₄_eq (w.maximalIdeal.adicCompletionIntegers F) W]
  exact norm_algebraMap_le_one w _

end Integral

section Reduction
variable {F : Type*} [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
  (w : FinitePlace F)

/-- The `j`-invariant is integral at each place of good reduction. -/
lemma valuation_j_le_one_of_good (hw : HasGoodReductionAt E w) :
    w.maximalIdeal.valuation F E.j ≤ 1 := by
  obtain ⟨C, hC⟩ := hw
  haveI : ((C • E).baseChange (w.maximalIdeal.adicCompletion F)).HasGoodReduction
    (w.maximalIdeal.adicCompletionIntegers F) := hC
  have hΔ : ‖((C • E).baseChange (w.maximalIdeal.adicCompletion F)).Δ‖ = 1 :=
    (valuation_eq_one_iff w _).1 HasGoodReduction.goodReduction
  have hc₄ : ‖((C • E).baseChange (w.maximalIdeal.adicCompletion F)).c₄‖ ≤ 1 := norm_c₄_le_one _
  rw [baseChange_adicCompletion_eq, map_Δ] at hΔ
  rw [baseChange_adicCompletion_eq, map_c₄] at hc₄
  rw [← variableChange_j E C, ← norm_emb_le_one_iff, j_eq_inv_Δ_mul, map_mul, map_inv₀,
    map_pow, norm_mul, norm_inv, norm_pow, hΔ, inv_one, one_mul]
  exact pow_le_one₀ (norm_nonneg _) hc₄

lemma hasMultiplicativeReductionAt_iff_of_stable (hst : HasStableReductionAt E w) :
    HasMultiplicativeReductionAt E w ↔ ¬ w.maximalIdeal.valuation F E.j ≤ 1 := by
  constructor
  · intro hw
    exact not_le.2 (one_lt_valuation_j_of_mult E w hw)
  · intro h
    rcases hst with hg | hm
    · exact absurd (valuation_j_le_one_of_good E w hg) h
    · exact hm

end Reduction
end AbcAdaptation.Reference.Iut

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField
open scoped Real

variable (P : CurveProviders) (x : Pt)

/-- A place outside the multiplicative locus contributes zero to the finite height of `j`. -/
theorem posLog_j_eq_zero_of_not_mem_badAll {w : FinitePlace (P.curve x).F}
    (hw : w ∉ (P.curve x).badAll) : log⁺ (w (P.curve x).E.j) = 0 := by
  have hst := (P.arith x).stable_reduction w
  have hle : w.maximalIdeal.valuation _ (P.curve x).E.j ≤ 1 := by
    by_contra h
    exact hw ((hasMultiplicativeReductionAt_iff_of_stable (P.curve x).E w hst).mpr h)
  rw [Real.posLog_eq_zero_iff, abs_of_nonneg (apply_nonneg _ _), ← FinitePlace.norm_embedding_eq]
  exact (norm_emb_le_one_iff _).mpr hle

end AbcAdaptation.Tripod
