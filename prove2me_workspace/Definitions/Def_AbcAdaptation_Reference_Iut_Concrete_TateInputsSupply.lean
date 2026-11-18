/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib.Tactic.NormNum
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_UniformizerSupply
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_CurveData
import Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_QParameter_JExistence

namespace AbcAdaptation.Reference.Iut

universe u
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing
  IsLocalRing WeierstrassCurve NumberField TateCurvesTheta
open scoped WithZero

section General

variable {k : Type*} [Field k] (R : Type*) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [Algebra R k] [IsFractionRing R k]
  {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation k Γ)

/-- For a DVR `R` with fraction field `k`, an element of `k` has `maximalIdeal`-adic valuation
`≤ 1` if and only if it lies in the image of `R`. -/
lemma valuation_maximalIdeal_le_one_iff (x : k) :
    valuation k (maximalIdeal R) x ≤ 1 ↔ ∃ r : R, algebraMap R k r = x :=
  ⟨fun hx => exists_lift_of_le_one hx, fun ⟨r, hr⟩ => hr ▸ valuation_le_one _ r⟩

/-- If the valuation ring of `v` is (the image of) `R`, then the `maximalIdeal`-adic valuation
of `R` is equivalent to `v`. -/
lemma valuation_isEquiv_of_range (h : ∀ x : k, v x ≤ 1 ↔ ∃ r : R, algebraMap R k r = x) :
    (valuation k (maximalIdeal R)).IsEquiv v := by
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  rw [valuation_maximalIdeal_le_one_iff, h]

end General
section Local

variable {F : Type*} [Field F] [NumberField F] (w : FinitePlace F)

/-- The valuation ring of `Valued.v` on `F_w` is `𝒪_w = adicCompletionIntegers`, as the range
of the inclusion. -/
lemma valued_le_one_iff_range (x : localCompletion w) :
    Valued.v x ≤ 1 ↔
      ∃ r : w.maximalIdeal.adicCompletionIntegers F,
        algebraMap (w.maximalIdeal.adicCompletionIntegers F) (localCompletion w) r = x := by
  rw [← mem_adicCompletionIntegers]
  exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨r, hr⟩ => hr ▸ r.2⟩

/-- The `maximalIdeal`-adic valuation of `𝒪_w` on `F_w` is equivalent to the valuation
`Valued.v` of the completion. -/
lemma valuation_isEquiv_valued :
    (valuation (localCompletion w) (maximalIdeal (w.maximalIdeal.adicCompletionIntegers F))).IsEquiv
      (Valued.v : Valuation (localCompletion w) ℤᵐ⁰) :=
  valuation_isEquiv_of_range _ _ (valued_le_one_iff_range w)

/-- `v_w(x) < 1 ↔ ‖x‖ < 1` on `F_w`. -/
lemma valuation_lt_one_iff (x : localCompletion w) :
    valuation (localCompletion w) (maximalIdeal (w.maximalIdeal.adicCompletionIntegers F)) x < 1 ↔
      ‖x‖ < 1 := by
  rw [norm_lt_one_iff_valued]
  exact (valuation_isEquiv_valued w).lt_one_iff_lt_one

/-- `v_w(x) = 1 ↔ ‖x‖ = 1` on `F_w`. -/
lemma valuation_eq_one_iff (x : localCompletion w) :
    valuation (localCompletion w) (maximalIdeal (w.maximalIdeal.adicCompletionIntegers F)) x = 1 ↔
      ‖x‖ = 1 := by
  rw [norm_eq_one_iff_valued]
  exact (valuation_isEquiv_valued w).eq_one_iff_eq_one

end Local

section Multiplicative

variable {F : Type*} [Field F] [NumberField F] {w : FinitePlace F}
  (W : WeierstrassCurve (localCompletion w))
section MultReduction

variable [W.HasMultiplicativeReduction (w.maximalIdeal.adicCompletionIntegers F)]

/-- Multiplicative reduction: `‖c₄‖ = 1`. -/
lemma norm_c₄_eq_one : ‖W.c₄‖ = 1 :=
  (valuation_eq_one_iff w _).1 HasMultiplicativeReduction.multiplicativeReduction

/-- Bad reduction: `‖Δ‖ < 1`. -/
lemma norm_Δ_lt_one : ‖W.Δ‖ < 1 :=
  (valuation_lt_one_iff w _).1 HasMultiplicativeReduction.badReduction

end MultReduction
end Multiplicative

section Mult

variable {F : Type*} [Field F] [NumberField F] (E : WeierstrassCurve F) (w : FinitePlace F)

lemma baseChange_adicCompletion_eq :
    E.baseChange (w.maximalIdeal.adicCompletion F) = E.map (FinitePlace.embedding w.maximalIdeal) :=
  rfl

section Model

variable [(E.baseChange (w.maximalIdeal.adicCompletion F)).HasMultiplicativeReduction
  (w.maximalIdeal.adicCompletionIntegers F)]

/-- `v_w(c₄(E)) = 1` for a model `E` whose base change has multiplicative reduction. -/
lemma valuation_c₄_eq_one_of_baseChange : w.maximalIdeal.valuation F E.c₄ = 1 := by
  have h := norm_c₄_eq_one (E.baseChange (w.maximalIdeal.adicCompletion F))
  rw [baseChange_adicCompletion_eq, map_c₄, norm_eq_one_iff_valued, FinitePlace.embedding_apply,
    valuedAdicCompletion_eq_valuation'] at h
  exact h

/-- `v_w(Δ(E)) < 1` for a model `E` whose base change has multiplicative reduction. -/
lemma valuation_Δ_lt_one_of_baseChange : w.maximalIdeal.valuation F E.Δ < 1 := by
  have h := norm_Δ_lt_one (E.baseChange (w.maximalIdeal.adicCompletion F))
  rw [baseChange_adicCompletion_eq, map_Δ, norm_lt_one_iff_valued, FinitePlace.embedding_apply,
    valuedAdicCompletion_eq_valuation'] at h
  exact h

end Model

/-- At a place of multiplicative reduction there is a global change of variables `C` such that
the model `C • E` has multiplicative reduction over the completed integers (Mathlib's class),
with `v_w(c₄(C • E)) = 1` and `v_w(Δ(C • E)) < 1`. -/
lemma exists_variableChange_of_mult (hw : HasMultiplicativeReductionAt E w) :
    ∃ C : VariableChange F,
      ((C • E).baseChange (w.maximalIdeal.adicCompletion F)).HasMultiplicativeReduction
        (w.maximalIdeal.adicCompletionIntegers F) ∧
      w.maximalIdeal.valuation F (C • E).c₄ = 1 ∧ w.maximalIdeal.valuation F (C • E).Δ < 1 := by
  obtain ⟨C, hC⟩ := hw
  exact ⟨C, hC, valuation_c₄_eq_one_of_baseChange (C • E) w,
    valuation_Δ_lt_one_of_baseChange (C • E) w⟩

omit [NumberField F] in
lemma j_eq_inv_Δ_mul [E.IsElliptic] : E.j = E.Δ⁻¹ * E.c₄ ^ 3 := by
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, coe_Δ']

/-- `v_w(j(E)) > 1` at a place of multiplicative reduction (the `j`-invariant is invariant
under changes of variables). -/
lemma one_lt_valuation_j_of_mult [E.IsElliptic] (hw : HasMultiplicativeReductionAt E w) :
    1 < w.maximalIdeal.valuation F E.j := by
  obtain ⟨C, -, hc₄, hΔ⟩ := exists_variableChange_of_mult E w hw
  have hΔ0 : (C • E).Δ ≠ 0 := by rw [← coe_Δ']; exact (C • E).Δ'.ne_zero
  have hpos : 0 < w.maximalIdeal.valuation F (C • E).Δ := by
    rw [pos_iff_ne_zero]
    exact (Valuation.ne_zero_iff _).2 hΔ0
  rw [← variableChange_j E C, j_eq_inv_Δ_mul, map_mul, map_inv₀, map_pow, hc₄, one_pow, mul_one]
  exact (one_lt_inv₀ hpos).2 hΔ

end Mult
section Norm
variable {K : Type*} [Field K] [NumberField K] {w : FinitePlace K}

/-- The norm on the completion `K_w` of the image of `y ∈ K`, in terms of the valuation. -/
lemma norm_emb_le_one_iff (y : K) :
    ‖(FinitePlace.embedding w.maximalIdeal y : localCompletion w)‖ ≤ 1 ↔
      w.maximalIdeal.valuation K y ≤ 1 := by
  rw [norm_le_one_iff_valued, FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation']

end Norm
section Twelve
variable {k : Type*} [Field k] [NumberField k]

/-- `12 ≠ 0` on the completion (characteristic zero). -/
lemma twelve_ne_zero (w : FinitePlace k) : (12 : localCompletion w) ≠ 0 := by
  have : (12 : localCompletion w) = FinitePlace.embedding w.maximalIdeal 12 := by
    rw [map_ofNat]
  rw [this]
  exact (map_ne_zero (FinitePlace.embedding w.maximalIdeal)).mpr (by norm_num)
end Twelve
namespace EllipticCurveData

variable (C : EllipticCurveData.{u})

/-- At a place of multiplicative reduction, the `j`-invariant has norm `> 1` in `F_w`
(`Iut.one_lt_valuation_j_of_mult`, via a minimal model `C • E`). -/
lemma one_lt_norm_j {w : FinitePlace C.F} (hw : w ∈ C.badAll) :
    1 < ‖FinitePlace.embedding w.maximalIdeal C.E.j‖ :=
  not_le.1 fun h => not_le.2 (one_lt_valuation_j_of_mult C.E w hw) ((norm_emb_le_one_iff _).1 h)

/-- The Tate parameter of `E` at a place of multiplicative reduction: the unique Tate
parameter of `F_w` whose Tate curve has `j`-invariant `j(E)`. -/
noncomputable def tateParameter {w : FinitePlace C.F} (hw : w ∈ C.badAll) :
    TateParameter (localCompletion w) :=
  (TateParameter.exists_tateParameter_tateJ_eq (twelve_ne_zero w) (C.one_lt_norm_j hw)).choose

lemma tateParameter_tateJ {w : FinitePlace C.F} (hw : w ∈ C.badAll) :
    (C.tateParameter hw).tateJ = FinitePlace.embedding w.maximalIdeal C.E.j :=
  (TateParameter.exists_tateParameter_tateJ_eq (twelve_ne_zero w)
    (C.one_lt_norm_j hw)).choose_spec

/-- **The Tate inputs** of an elliptic curve over a number field: Tate parameters at the
multiplicative places, via the `j`-parametrization of Tate curves, and uniformizers of the
completions. -/
noncomputable def tateInputs : C.TateInputs where
  tate _ hw := C.tateParameter hw
  tateJ_eq _ hw := C.tateParameter_tateJ hw
  unif w _ := (exists_isUniformizer w).choose
  unif_isUniformizer w _ := (exists_isUniformizer w).choose_spec

end EllipticCurveData

end AbcAdaptation.Reference.Iut
