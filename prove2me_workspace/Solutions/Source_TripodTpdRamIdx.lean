/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Tripod/TpdRamIdx.lean and Iut/Tripod/Tower.lean
-/
import Solutions.Source_TripodTpdGalois
import Solutions.Source_ReferenceIutTowerInertia
import Solutions.Source_TripodLegendreValuationBounds
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_JTransport
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_TateInputsSupply
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Ramification of the Legendre tripodal field at the bad places

A pole of the Legendre j-invariant yields a generator of valuation less than one.
At most two conjugates of this generator are congruent to it at the chosen place.
The inertia group acts faithfully on that generator, so the ramification index is at most two.
-/

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum Polynomial
open scoped IntermediateField WithZero

section Inertia

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K]
  [Algebra k K] [IsGalois k K]

/-- Bound the ramification index by two when an integral field generator has at most two
conjugates congruent to it at the chosen place. -/
lemma relRamIdx_le_two_of_generator {w : FinitePlace K} {v : FinitePlace k}
    (hwv : FinitePlace.LiesOver w v) {a : K} (ha : IntermediateField.adjoin k {a} = ⊤)
    (hav : w.maximalIdeal.valuation K a ≤ 1) {b c : K}
    (hconj : ∀ σ : K ≃ₐ[k] K, w.maximalIdeal.valuation K (σ a - a) < 1 →
      σ a = b ∨ σ a = c) : relRamIdx w v ≤ 2 := by
  classical
  have hadj : Algebra.adjoin k {a} = ⊤ := by
    have hint : IsAlgebraic k a := (IsIntegral.of_finite k a).isAlgebraic
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint, ha,
      IntermediateField.top_toSubalgebra]
  rw [AbcAdaptation.Reference.Iut.relRamIdx_eq_card_inertia hwv]
  let f : w.maximalIdeal.asIdeal.inertia (K ≃ₐ[k] K) → ({b, c} : Finset K) := fun σ =>
    ⟨σ.1 a, by
      rcases hconj σ.1 (valuation_sub_lt_one_of_mem_inertia σ.2 hav) with h | h <;> simp [h]⟩
  have hf : Function.Injective f := by
    intro σ τ h
    have h' : σ.1 a = τ.1 a := congrArg Subtype.val h
    have hst : (σ.1 : K →ₐ[k] K) = τ.1 :=
      AlgHom.ext_of_adjoin_eq_top hadj fun y hy => by
        rw [Set.mem_singleton_iff.mp hy]
        exact h'
    exact Subtype.ext (AlgEquiv.ext fun y => AlgHom.congr_fun hst y)
  calc
    Nat.card (w.maximalIdeal.asIdeal.inertia (K ≃ₐ[k] K)) ≤
        Nat.card ({b, c} : Finset K) := Nat.card_le_card_of_injective f hf
    _ = ({b, c} : Finset K).card := Nat.card_eq_finsetCard _
    _ ≤ 2 := Finset.card_le_two

end Inertia

section Sextic

variable {L : Type*} [Field L] {l : L}

private lemma legendreJ_inv (hl0 : l ≠ 0) (hl1 : l - 1 ≠ 0) :
    legendreJ l⁻¹ = legendreJ l := by
  have h1' : 1 - l ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hl1).symm
  have e1 : l⁻¹ ^ 2 - l⁻¹ + 1 = (l ^ 2 - l + 1) / l ^ 2 := by
    field_simp
    ring
  have e2 : l⁻¹ - 1 = (1 - l) / l := by
    rw [eq_div_iff hl0, sub_mul, inv_mul_cancel₀ hl0, one_mul]
  have hd_inv : l⁻¹ ^ 2 * ((1 - l) / l) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (inv_ne_zero hl0)) (pow_ne_zero _ (div_ne_zero h1' hl0))
  have hd : l ^ 2 * (l - 1) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ hl1)
  unfold legendreJ
  rw [e1, e2, div_eq_div_iff hd_inv hd]
  field_simp
  ring

private lemma legendreJ_one_sub : legendreJ (1 - l) = legendreJ l := by
  have e1 : (1 - l) ^ 2 - (1 - l) + 1 = l ^ 2 - l + 1 := by ring
  have e2 : 1 - l - 1 = -l := by ring
  have e3 : (1 - l) ^ 2 = (l - 1) ^ 2 := by ring
  unfold legendreJ
  rw [e1, e2, neg_sq, e3]
  ring

private lemma sexticEval_legendreJ_self (hl0 : l ≠ 0) (hl1 : l - 1 ≠ 0) :
    sexticEval (legendreJ l) l = 0 := by
  rw [sexticEval, legendreJ,
    div_mul_cancel₀ _ (mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ hl1)), sub_self]

private lemma eq_or_eq_of_valuation_sub_lt_one [CharZero L] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ) (hl0 : l ≠ 0)
    (hl : v l < 1) {s : L} (hs : sexticEval (legendreJ l) s = 0)
    (hsub : v (s - l) < 1) : s = l ∨ s = l / (l - 1) := by
  have hsv : v s < 1 := by
    simpa only [sub_add_cancel] using v.map_add_lt hsub hl
  have hl1 : l - 1 ≠ 0 := fun h => by
    rw [sub_eq_zero.mp h, map_one] at hl
    exact lt_irrefl _ hl
  have hvl : 0 < v l := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr hl0)
  have h1l : v (1 - l) = 1 := by
    rw [Valuation.map_sub_eq_of_lt_left v (by rwa [map_one]), map_one]
  have hl1' : v (l - 1) = 1 := (v.map_sub_swap l 1).trans h1l
  rcases eq_of_sexticEval_legendreJ_eq_zero hl0 hl1 hs with h | h | h | h | h | h
  · exact Or.inl h
  · rw [h, h1l] at hsv
    exact absurd hsv (lt_irrefl _)
  · rw [h, map_inv₀] at hsv
    exact absurd ((one_lt_inv₀ hvl).mpr hl) (not_lt.mpr hsv.le)
  · rw [h, map_inv₀, h1l, inv_one] at hsv
    exact absurd hsv (lt_irrefl _)
  · exact Or.inr h
  · rw [h, map_div₀, hl1', one_div] at hsv
    exact absurd ((one_lt_inv₀ hvl).mpr hl) (not_lt.mpr hsv.le)

private lemma valuation_lt_one_of_one_lt_legendreJ (v : Valuation L ℤᵐ⁰)
    (h256 : v 256 ≤ 1) (hj : 1 < v (legendreJ l)) :
    v l < 1 ∨ v l⁻¹ < 1 ∨ v (1 - l) < 1 := by
  rcases legendre_valuation_cases v (l := l) with
    ⟨hv, _, _⟩ | ⟨_, hv, _⟩ | ⟨hvl, hvl1, hvpoly⟩ | ⟨hv, _, _⟩
  · exact Or.inl hv
  · exact Or.inr (Or.inr ((v.map_sub_swap 1 l).trans_lt hv))
  · have hle : v (legendreJ l) ≤ 1 := by
      simp only [legendreJ, map_div₀, map_mul, map_pow, hvl, hvl1, one_pow, mul_one, div_one]
      exact mul_le_one₀ h256 zero_le (pow_le_one₀ zero_le hvpoly)
    exact (not_lt_of_ge hle hj).elim
  · exact Or.inr (Or.inl (by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hv))

end Sextic

section Tripodal

variable (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5)

/-- The Legendre parameter as an element of the tripodal field. -/
noncomputable def lamTpd : tpdC x h3 h5 :=
  ⟨genC x h3 h5, (mem_tpdC_iff x h3 h5 _).mpr (IntermediateField.mem_adjoin_simple_self ℚ _)⟩

@[simp] lemma coe_lamTpd : (lamTpd x h3 h5 : (curveOf x h3 h5).F) = genC x h3 h5 := rfl

/-- The modular invariant as an element of the tripodal field. -/
noncomputable def jTpd : tpdC x h3 h5 :=
  algebraMap (modC x h3 h5) (tpdC x h3 h5) (jCpt x h3 h5)

lemma coe_jTpd : (jTpd x h3 h5 : (curveOf x h3 h5).F) = (curveOf x h3 h5).E.j := by
  rw [jTpd, algebraMap_fieldOfModuli_tripodal_apply, coe_jC]

lemma lamTpd_ne_zero : lamTpd x h3 h5 ≠ 0 := fun h =>
  genC_ne_zero x h3 h5 (congrArg Subtype.val h)

lemma lamTpd_sub_one_ne_zero : lamTpd x h3 h5 - 1 ≠ 0 := by
  intro h
  have h' := congrArg Subtype.val h
  change genC x h3 h5 - 1 = 0 at h'
  exact genC_ne_one x h3 h5 (sub_eq_zero.mp h')

lemma jTpd_eq : jTpd x h3 h5 = legendreJ (lamTpd x h3 h5) := by
  apply (algebraMap (tpdC x h3 h5) (curveOf x h3 h5).F).injective
  rw [map_legendreJ]
  change (jTpd x h3 h5 : (curveOf x h3 h5).F) = legendreJ (genC x h3 h5)
  rw [coe_jTpd]
  exact j_eq x h3 h5

/-- The Legendre parameter generates the tripodal field over the field of moduli. -/
lemma adjoin_lamTpd_eq_top : IntermediateField.adjoin (modC x h3 h5) {lamTpd x h3 h5} = ⊤ := by
  rw [eq_top_iff]
  intro t _
  have ht : (t : (curveOf x h3 h5).F) ∈ (modC x h3 h5)⟮genC x h3 h5⟯ :=
    (mem_adjoin_modC_iff x h3 h5 _).mpr ((mem_tpdC_iff x h3 h5 _).mp t.2)
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff _ _).mp ht
  rw [IntermediateField.mem_adjoin_simple_iff]
  have hEval (p : (modC x h3 h5)[X]) :
      algebraMap (tpdC x h3 h5) (curveOf x h3 h5).F (aeval (lamTpd x h3 h5) p) =
        aeval (genC x h3 h5) p := by
    rw [← aeval_algebraMap_apply, IntermediateField.algebraMap_apply, coe_lamTpd]
  refine ⟨r, s, (algebraMap (tpdC x h3 h5) (curveOf x h3 h5).F).injective ?_⟩
  rw [map_div₀, hEval, hEval]
  exact hrs

private lemma sexticEval_jTpd_algEquiv (σ : tpdC x h3 h5 ≃ₐ[modC x h3 h5] tpdC x h3 h5)
    (s : tpdC x h3 h5) :
    sexticEval (jTpd x h3 h5) (σ s) = σ (sexticEval (jTpd x h3 h5) s) := by
  simp only [sexticEval, jTpd, map_sub, map_mul, map_pow, map_add, map_one, map_ofNat,
    AlgEquiv.commutes]

/-- The tripodal extension has ramification index at most two above a pole of j. -/
theorem relRamIdx_tpd_le_two_of_one_lt_valuation (u : FinitePlace (tpdC x h3 h5))
    (u₀ : FinitePlace (modC x h3 h5)) (huu₀ : FinitePlace.LiesOver u u₀)
    (hj : 1 < u₀.maximalIdeal.valuation (modC x h3 h5) (jCpt x h3 h5)) :
    relRamIdx u u₀ ≤ 2 := by
  letI : IsGalois (modC x h3 h5) (tpdC x h3 h5) := isGalois_tpd x h3 h5
  let v := u.maximalIdeal.valuation (tpdC x h3 h5)
  let l := lamTpd x h3 h5
  have hl0 : l ≠ 0 := lamTpd_ne_zero x h3 h5
  have hl1 : l - 1 ≠ 0 := lamTpd_sub_one_ne_zero x h3 h5
  have hjT : 1 < v (jTpd x h3 h5) := by
    change 1 < u.maximalIdeal.valuation (tpdC x h3 h5)
      (algebraMap (modC x h3 h5) (tpdC x h3 h5) (jCpt x h3 h5))
    rw [valuation_algebraMap_eq_pow huu₀]
    exact one_lt_pow₀ hj (ramificationIdx'_ne_zero huu₀)
  have hjEq : jTpd x h3 h5 = legendreJ l := jTpd_eq x h3 h5
  rw [hjEq] at hjT
  have hgen : IntermediateField.adjoin (modC x h3 h5) {l} = ⊤ := adjoin_lamTpd_eq_top x h3 h5
  have bound (a : tpdC x h3 h5) (ha0 : a ≠ 0)
      (hadj : IntermediateField.adjoin (modC x h3 h5) {a} = ⊤)
      (hja : jTpd x h3 h5 = legendreJ a) (hva : v a < 1) : relRamIdx u u₀ ≤ 2 := by
    refine relRamIdx_le_two_of_generator huu₀ hadj hva.le (b := a) (c := a / (a - 1)) ?_
    intro σ hσ
    have ha1 : a - 1 ≠ 0 := fun h => by
      rw [sub_eq_zero.mp h, map_one] at hva
      exact lt_irrefl _ hva
    have hroot : sexticEval (legendreJ a) (σ a) = 0 := by
      rw [← hja, sexticEval_jTpd_algEquiv, hja, sexticEval_legendreJ_self ha0 ha1, map_zero]
    exact eq_or_eq_of_valuation_sub_lt_one v ha0 hva hroot hσ
  rcases valuation_lt_one_of_one_lt_legendreJ v (valuation_256_le_one u) hjT with h | h | h
  · exact bound l hl0 hgen hjEq h
  · refine bound l⁻¹ (inv_ne_zero hl0) ?_ (hjEq.trans (legendreJ_inv hl0 hl1).symm) h
    rw [eq_top_iff, ← hgen, IntermediateField.adjoin_simple_le_iff]
    simpa only [inv_inv] using inv_mem (IntermediateField.mem_adjoin_simple_self (modC x h3 h5) l⁻¹)
  · refine bound (1 - l) (sub_ne_zero.mpr (sub_ne_zero.mp hl1).symm) ?_
      (hjEq.trans (legendreJ_one_sub (l := l)).symm) h
    rw [eq_top_iff, ← hgen, IntermediateField.adjoin_simple_le_iff]
    simpa only [sub_sub_cancel] using
      sub_mem (one_mem _) (IntermediateField.mem_adjoin_simple_self (modC x h3 h5) (1 - l))

/-- The modular invariant has a pole at each bad place of the field of moduli. -/
lemma one_lt_valuation_jCpt_of_mem_VBadOf {ℓ : ℕ} {u₀ : FinitePlace (modC x h3 h5)}
    (hu₀ : u₀ ∈ (curveOf x h3 h5).VBadOf ℓ) :
    1 < u₀.maximalIdeal.valuation (modC x h3 h5) (jCpt x h3 h5) := by
  obtain ⟨-, -, ⟨w, hwu₀⟩, hmult⟩ := hu₀
  have hj := one_lt_valuation_j_of_mult (curveOf x h3 h5).E w (hmult w hwu₀)
  have hval := valuation_algebraMap_eq_pow hwu₀ (jCpt x h3 h5)
  simp only [IntermediateField.algebraMap_apply, coe_jC] at hval
  rw [hval] at hj
  exact lt_of_not_ge fun hle => (not_lt_of_ge (pow_le_one₀ zero_le hle)) hj

/-- IUT IV, Proposition 1.8 for the bad places of the tripodal extension. -/
theorem relRamIdx_tpd_le_two (ℓ : ℕ) (u : FinitePlace (tpdC x h3 h5))
    (u₀ : FinitePlace (modC x h3 h5)) (hu₀ : u₀ ∈ (curveOf x h3 h5).VBadOf ℓ)
    (huu₀ : FinitePlace.LiesOver u u₀) : relRamIdx u u₀ ≤ 2 :=
  relRamIdx_tpd_le_two_of_one_lt_valuation x h3 h5 u u₀ huu₀
    (one_lt_valuation_jCpt_of_mem_VBadOf x h3 h5 hu₀)

end Tripodal

/-- The ramification bound at the bad places of the curve of a tripod point. -/
theorem relRamIdxModLeTwo_curve (P : CurveProviders) (x : Pt) (ℓ : ℕ) :
    RelRamIdxModLeTwo (P.curve x).E ((P.curve x).VBadOf ℓ) :=
  fun u u₀ hu₀ huu₀ =>
    relRamIdx_tpd_le_two x (P.torsionFinite3 x.1) (P.torsionFinite5 x.1) ℓ u u₀ hu₀ huu₀

end AbcAdaptation.Tripod
