/-
Adapted from Iut/Cor312/ThetaData/BadPlaceNorm.lean,
Iut/Cor312/ThetaData/SqrtAtBadPlace.lean, Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean,
and Iut/Cor312/ThetaData/TateIsomorphism.lean.
Source snapshot 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8, lana-agents/iut.
Upstream commits cfc9e36c8984a83c9199ccbb8d1b30d9c130edf6,
e4777b2238f45be2e58c00b4d0213c0cb83405b9 and 09d74a40f46688fa5e4eba46ead73cb37d6abbe2.
Git author Christian Merten.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_TateInputsSupply
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_TateFamily
import Solutions.Source_TripodPlaceUnder
import Solutions.Source_TripodRelativeDegreeTower
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace AbcAdaptation.Reference.Iut

open NumberField WeierstrassCurve IsDedekindDomain.HeightOneSpectrum TateCurvesTheta
open scoped Classical Valued

universe u

noncomputable section

section Tangent

variable {k : Type*} [NormedField k]

/-- The tangent quadratic obtained from the coefficients of the Weierstrass equation. -/
def tangentQuadratic (W : WeierstrassCurve k) (r : k) : k :=
  W.c₄ * r ^ 2 + W.a₁ * W.c₄ * r - (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)

lemma tangent_sq_eq (W : WeierstrassCurve k) (r : k) :
    (2 * W.c₄ * r + W.a₁ * W.c₄) ^ 2 =
      -(W.c₄ * W.c₆) + 4 * W.c₄ * tangentQuadratic W r := by
  simp only [tangentQuadratic, c₄, c₆, b₂, b₄, b₆]
  ring

lemma exists_tangent_root_of_sq (W : WeierstrassCurve k) (h2 : (2 : k) ≠ 0)
    (hc₄ : W.c₄ ≠ 0) {s : k} (hs : s ^ 2 = -(W.c₄ * W.c₆)) :
    ∃ r : k, ‖tangentQuadratic W r‖ < 1 := by
  let r := (s - W.a₁ * W.c₄) / (2 * W.c₄)
  refine ⟨r, ?_⟩
  have hr : 2 * W.c₄ * r + W.a₁ * W.c₄ = s := by
    change 2 * W.c₄ * ((s - W.a₁ * W.c₄) / (2 * W.c₄)) + W.a₁ * W.c₄ = s
    rw [mul_div_cancel₀ _ (mul_ne_zero h2 hc₄)]
    exact sub_add_cancel _ _
  have h := tangent_sq_eq W r
  rw [hr, hs] at h
  have hzero : -(W.c₄ * W.c₆) + 4 * W.c₄ * tangentQuadratic W r =
      -(W.c₄ * W.c₆) + 0 := by
    rw [add_zero]
    exact h.symm
  have h4 : (4 : k) ≠ 0 := by
    rw [show (4 : k) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hf := (mul_eq_zero.mp (add_left_cancel hzero)).resolve_left (mul_ne_zero h4 hc₄)
  rw [hf, norm_zero]
  exact zero_lt_one

lemma sq_neg_c₄_mul_c₆_variableChange (W : WeierstrassCurve k) (C : VariableChange k)
    {s : k} (hs : s ^ 2 = -(W.c₄ * W.c₆)) :
    (((C.u⁻¹ : kˣ) : k) ^ 5 * s) ^ 2 = -((C • W).c₄ * (C • W).c₆) := by
  rw [mul_pow, hs, variableChange_c₄, variableChange_c₆]
  ring

/-- The norm of the j-invariant of a multiplicative model is greater than one. -/
lemma one_lt_norm_j_of_norms (W : WeierstrassCurve k) [W.IsElliptic]
    (hc₄ : ‖W.c₄‖ = 1) (hΔ : ‖W.Δ‖ < 1) : 1 < ‖W.j‖ := by
  have hΔ0 : W.Δ ≠ 0 := by
    rw [← coe_Δ']
    exact W.Δ'.ne_zero
  rw [j, Units.val_inv_eq_inv_val, coe_Δ', norm_mul, norm_inv, norm_pow, hc₄, one_pow, mul_one]
  exact (one_lt_inv₀ (norm_pos_iff.mpr hΔ0)).mpr hΔ

end Tangent

section Completions

variable {F : Type u} [Field F] [NumberField F]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
variable (E : WeierstrassCurve F) (K : IntermediateField F Fbar) [NumberField ↥K]

lemma curveKw_variableChange (C : VariableChange F) (w : FinitePlace ↥K) :
    curveKw (C • E) K w = ((C.map (algebraMap F ↥K)).map (emb K w)) • curveKw E K w := by
  rw [curveKw, curveK, map_variableChange, map_variableChange]

lemma neg_c₄_mul_c₆_curveKw (w : FinitePlace ↥K) :
    -((curveKw E K w).c₄ * (curveKw E K w).c₆) =
      emb K w (algebraMap F ↥K (-(E.c₄ * E.c₆))) := by
  simp only [curveKw, curveK, map_c₄, map_c₆, map_neg, map_mul]

variable {w : FinitePlace ↥K} {v : FinitePlace F}

lemma norm_c₄_curveKw (hwv : FinitePlace.LiesOver w v)
    (hc₄ : v.maximalIdeal.valuation F E.c₄ = 1) :
    ‖(curveKw E K w).c₄‖ = 1 := by
  rw [curveKw, curveK, map_c₄, map_c₄, emb, norm_eq_one_iff_valued,
    FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation',
    Tripod.valuation_algebraMap_eq_pow hwv, hc₄, one_pow]

lemma norm_Δ_curveKw (hwv : FinitePlace.LiesOver w v)
    (hΔ : v.maximalIdeal.valuation F E.Δ < 1) :
    ‖(curveKw E K w).Δ‖ < 1 := by
  rw [curveKw, curveK, map_Δ, map_Δ, emb, norm_lt_one_iff_valued,
    FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation',
    Tripod.valuation_algebraMap_eq_pow hwv]
  exact pow_lt_one₀ zero_le hΔ (Tripod.ramificationIdx'_ne_zero hwv)

variable [E.IsElliptic] {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}

lemma mult_placeUnder
    (hmult : ∀ v ∈ VBad, ∀ v₀ : FinitePlace F, FinitePlace.LiesOver v₀ v →
      HasMultiplicativeReductionAt E v₀)
    (hw : IsBadPlace E K VBad w) :
    HasMultiplicativeReductionAt E (Tripod.placeUnder w : FinitePlace F) := by
  obtain ⟨v, hv, hwv⟩ := hw
  refine hmult v hv _ ⟨?_⟩
  haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hwv
  rw [hwv.over, Tripod.placeUnder_maximalIdeal, Ideal.under_def, Ideal.under_def,
    Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]

lemma norm_two_curveKw (hVBad : ∀ v ∈ VBad, residueChar v ≠ 2)
    (hw : IsBadPlace E K VBad w) : ‖(2 : localCompletion w)‖ = 1 := by
  obtain ⟨v, hv, hwv⟩ := hw
  have h2 : residueChar w ≠ 2 := fun h =>
    hVBad v hv ((Tripod.residueChar_eq_of_liesOver hwv).symm.trans h)
  have hcast : (2 : localCompletion w) = emb K w (2 : ↥K) := by rw [map_ofNat]
  rw [hcast, emb, norm_eq_one_iff_valued, FinitePlace.embedding_apply,
    valuedAdicCompletion_eq_valuation']
  exact Tripod.valuation_two_eq_one_of_ne h2

end Completions

end

end AbcAdaptation.Reference.Iut
