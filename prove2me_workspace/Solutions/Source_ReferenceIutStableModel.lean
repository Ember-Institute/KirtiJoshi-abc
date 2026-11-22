/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/StableOdd.lean
-/
import Solutions.Source_ReferenceIutTowerIntegralTorsion
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_GlobalField
import ArithmeticTeichmullerSpaces.Act1Scene1.IutCompat.Cor312.ThetaData.ValuationTransfer
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.PlaceUnder
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open WeierstrassCurve

/-! ## Minimality of an integral model with a unit discriminant or a unit `c₄` -/

section Minimal

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

/-- The discriminant of an integral model has valuation `≤ 1`. -/
private lemma valuation_Δ_le_one_of_isIntegral (W : WeierstrassCurve K) [IsIntegral R W] :
    valuation K (maximalIdeal R) W.Δ ≤ 1 := by
  rw [← integralModel_Δ_eq R W]
  exact valuation_le_one _ _

/-- The invariant `c₄` of an integral model has valuation `≤ 1`. -/
private lemma valuation_c₄_le_one_of_isIntegral (W : WeierstrassCurve K) [IsIntegral R W] :
    valuation K (maximalIdeal R) W.c₄ ≤ 1 := by
  rw [← integralModel_c₄_eq R W]
  exact valuation_le_one _ _

/-- An integral model whose discriminant is a unit is minimal: every integral model has
`v(Δ) ≤ 1`. -/
private lemma isMinimal_of_valuation_Δ_eq_one (W : WeierstrassCurve K) [hW : IsIntegral R W]
    (h : valuation K (maximalIdeal R) W.Δ = 1) : IsMinimal R W := by
  refine ⟨⟨by simp only [one_smul]; exact hW, fun C hC _ => ?_⟩⟩
  simp only [one_smul] at hC ⊢
  haveI := hC
  rw [← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral, valuation_Δ_aux_eq_of_isIntegral, h]
  exact valuation_Δ_le_one_of_isIntegral R (C • W)

/-- An integral model whose invariant `c₄` is a unit is minimal: for an integral model
`C • W`, `v(u⁻¹)⁴ = v(c₄(C • W)) ≤ 1` forces `v(u⁻¹) ≤ 1`, hence
`v(Δ(C • W)) = v(u⁻¹)¹² v(Δ(W)) ≤ v(Δ(W))`. -/
private lemma isMinimal_of_valuation_c₄_eq_one (W : WeierstrassCurve K) [hW : IsIntegral R W]
    (h : valuation K (maximalIdeal R) W.c₄ = 1) : IsMinimal R W := by
  refine ⟨⟨by simp only [one_smul]; exact hW, fun C hC _ => ?_⟩⟩
  simp only [one_smul] at hC ⊢
  haveI := hC
  rw [← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral, valuation_Δ_aux_eq_of_isIntegral,
    variableChange_Δ, map_mul, map_pow]
  have hu : valuation K (maximalIdeal R) (C.u⁻¹ : Kˣ) ≤ 1 := by
    have hc := valuation_c₄_le_one_of_isIntegral R (C • W)
    rw [variableChange_c₄, map_mul, map_pow, h, mul_one] at hc
    exact (pow_le_one_iff_of_nonneg zero_le (by norm_num)).mp hc
  exact mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hu)

end Minimal

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open JoshiTeich.ReferenceIut (baseChange_adicCompletion_eq norm_emb_eq_one_iff
  norm_emb_lt_one_iff valuation_eq_one_iff valuation_lt_one_iff valued_le_one_iff_range)
open scoped WithZero

/-! ## Good and multiplicative models for a valuation -/

section Models

variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation K Γ) (E : WeierstrassCurve K)

/-- The model `E` is good for `v`: integral with a unit discriminant. -/
def IsGoodModel : Prop := IsIntegralModel v E ∧ v E.Δ = 1

/-- The model `E` is multiplicative for `v`: integral with a non-unit discriminant and a
unit `c₄`. -/
def IsMultModel : Prop := IsIntegralModel v E ∧ v E.Δ < 1 ∧ v E.c₄ = 1

/-- The model `E` is good or multiplicative for `v`. -/
def IsStableModel : Prop := IsGoodModel v E ∨ IsMultModel v E

variable {v E}

lemma IsIntegralModel.b₂ (h : IsIntegralModel v E) : v E.b₂ ≤ 1 := by
  obtain ⟨h₁, h₂, -, -, -⟩ := h
  rw [← Valuation.mem_integer_iff] at *
  exact add_mem (pow_mem h₁ 2) (mul_mem (ofNat_mem _ 4) h₂)

lemma IsIntegralModel.b₆ (h : IsIntegralModel v E) : v E.b₆ ≤ 1 := by
  obtain ⟨-, -, h₃, -, h₆⟩ := h
  rw [← Valuation.mem_integer_iff] at *
  exact add_mem (pow_mem h₃ 2) (mul_mem (ofNat_mem _ 4) h₆)

lemma IsIntegralModel.b₈ (h : IsIntegralModel v E) : v E.b₈ ≤ 1 := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := h
  rw [← Valuation.mem_integer_iff] at *
  exact sub_mem (add_mem (sub_mem (add_mem (mul_mem (pow_mem h₁ 2) h₆)
    (mul_mem (mul_mem (ofNat_mem _ 4) h₂) h₆)) (mul_mem (mul_mem h₁ h₃) h₄))
    (mul_mem h₂ (pow_mem h₃ 2))) (pow_mem h₄ 2)

lemma IsIntegralModel.Δ (h : IsIntegralModel v E) : v E.Δ ≤ 1 := by
  have h₂ := h.b₂
  have h₄ := h.b₄
  have h₆ := h.b₆
  have h₈ := h.b₈
  rw [← Valuation.mem_integer_iff] at *
  exact add_mem (sub_mem (sub_mem (mul_mem (neg_mem (pow_mem h₂ 2)) h₈)
    (mul_mem (ofNat_mem _ 8) (pow_mem h₄ 3))) (mul_mem (ofNat_mem _ 27) (pow_mem h₆ 2)))
    (mul_mem (mul_mem (mul_mem (ofNat_mem _ 9) h₂) h₄) h₆)

end Models

/-! ## From a stable model to stable reduction at a place -/

section Place

variable {F : Type*} [Field F] [NumberField F] (E : WeierstrassCurve F) (w : FinitePlace F)

/-- An element `y ∈ F` with `v_w(y) ≤ 1` lies in `𝒪_w`. -/
private lemma exists_adicCompletionIntegers_eq {y : F} (hy : w.maximalIdeal.valuation F y ≤ 1) :
    ∃ r : w.maximalIdeal.adicCompletionIntegers F,
      algebraMap (w.maximalIdeal.adicCompletionIntegers F) (w.maximalIdeal.adicCompletion F) r =
        FinitePlace.embedding w.maximalIdeal y :=
  (valued_le_one_iff_range w _).1
    (by rw [FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation']; exact hy)

/-- A `w`-integral model is integral over `𝒪_w` after base change to `F_w`. -/
private lemma isIntegral_baseChange_of_isIntegralModel
    (h : IsIntegralModel (w.maximalIdeal.valuation F) E) :
    (E.baseChange (w.maximalIdeal.adicCompletion F)).IsIntegral
      (w.maximalIdeal.adicCompletionIntegers F) := by
  rw [baseChange_adicCompletion_eq]
  exact isIntegral_of_exists_lift _ (exists_adicCompletionIntegers_eq w h.1)
    (exists_adicCompletionIntegers_eq w h.2.1) (exists_adicCompletionIntegers_eq w h.2.2.1)
    (exists_adicCompletionIntegers_eq w h.2.2.2.1) (exists_adicCompletionIntegers_eq w h.2.2.2.2)

/-- A good model at `w` has good reduction over `𝒪_w` in Mathlib's sense. -/
private lemma hasGoodReduction_baseChange_of_isGoodModel
    (h : IsGoodModel (w.maximalIdeal.valuation F) E) :
    (E.baseChange (w.maximalIdeal.adicCompletion F)).HasGoodReduction
      (w.maximalIdeal.adicCompletionIntegers F) := by
  haveI := isIntegral_baseChange_of_isIntegralModel E w h.1
  have hΔ : IsDedekindDomain.HeightOneSpectrum.valuation (w.maximalIdeal.adicCompletion F)
      (IsDiscreteValuationRing.maximalIdeal (w.maximalIdeal.adicCompletionIntegers F))
      (E.baseChange (w.maximalIdeal.adicCompletion F)).Δ = 1 := by
    rw [baseChange_adicCompletion_eq, map_Δ, valuation_eq_one_iff, norm_emb_eq_one_iff]
    exact h.2
  exact (hasGoodReduction_iff _ _).mpr ⟨isMinimal_of_valuation_Δ_eq_one _ _ hΔ, hΔ⟩

/-- A multiplicative model at `w` has multiplicative reduction over `𝒪_w` in Mathlib's sense. -/
private lemma hasMultiplicativeReduction_baseChange_of_isMultModel
    (h : IsMultModel (w.maximalIdeal.valuation F) E) :
    (E.baseChange (w.maximalIdeal.adicCompletion F)).HasMultiplicativeReduction
      (w.maximalIdeal.adicCompletionIntegers F) := by
  haveI := isIntegral_baseChange_of_isIntegralModel E w h.1
  have hc₄ : IsDedekindDomain.HeightOneSpectrum.valuation (w.maximalIdeal.adicCompletion F)
      (IsDiscreteValuationRing.maximalIdeal (w.maximalIdeal.adicCompletionIntegers F))
      (E.baseChange (w.maximalIdeal.adicCompletion F)).c₄ = 1 := by
    rw [baseChange_adicCompletion_eq, map_c₄, valuation_eq_one_iff, norm_emb_eq_one_iff]
    exact h.2.2
  have hΔ : IsDedekindDomain.HeightOneSpectrum.valuation (w.maximalIdeal.adicCompletion F)
      (IsDiscreteValuationRing.maximalIdeal (w.maximalIdeal.adicCompletionIntegers F))
      (E.baseChange (w.maximalIdeal.adicCompletion F)).Δ < 1 := by
    rw [baseChange_adicCompletion_eq, map_Δ, valuation_lt_one_iff, norm_emb_lt_one_iff]
    exact h.2.1
  exact (hasMultiplicativeReduction_iff _ _).mpr ⟨isMinimal_of_valuation_c₄_eq_one _ _ hc₄, hΔ, hc₄⟩

/-- **Stable reduction from a stable model**: if some change of variables `C • E` is a good or
multiplicative model at `w`, then `E` has stable reduction at `w`. -/
lemma hasStableReductionAt_of_isStableModel (C : VariableChange F)
    (h : IsStableModel (w.maximalIdeal.valuation F) (C • E)) : HasStableReductionAt E w := by
  rcases h with h | h
  · exact Or.inl ⟨C, hasGoodReduction_baseChange_of_isGoodModel _ w h⟩
  · exact Or.inr ⟨C, hasMultiplicativeReduction_baseChange_of_isMultModel _ w h⟩

end Place

end AbcAdaptation.Reference.Iut
