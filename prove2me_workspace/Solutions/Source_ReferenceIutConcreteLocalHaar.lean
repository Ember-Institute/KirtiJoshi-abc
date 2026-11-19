/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Concrete/LocalConstruct/Volume.lean and
  Iut/Concrete/LocalConstruct/Prop14.lean
-/
import Solutions.Source_ReferenceIutConcreteLocalIntegral
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicHaarScaling

/-!
# Finite-place Haar log-volume

The normalization uses the mass of the integral closure and the dimension over
`ℚ_p`, as in IUT III, Proposition 3.9(i). The inverse image under multiplication
by `p` has Haar mass multiplied by `p^[T : ℚ_p]`. This gives an additive
`log p` term for regions of positive finite mass when every factor lies over `p`.
-/

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.LocalConstruct

open MeasureTheory NumberField
open scoped ENNReal Pointwise

universe u

noncomputable section

variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K)

noncomputable instance instMeasurableSpaceFiniteTensor :
    MeasurableSpace (Tensor K (.finite p) c) := borel _

instance instBorelSpaceFiniteTensor : BorelSpace (Tensor K (.finite p) c) := ⟨rfl⟩

/-- Additive Haar measure on the finite-place packet. -/
def finiteHaar : Measure (Tensor K (.finite p) c) := Measure.addHaar

instance finiteHaar_isAddHaarMeasure : (finiteHaar p c).IsAddHaarMeasure :=
  inferInstanceAs (Measure.addHaar : Measure (Tensor K (.finite p) c)).IsAddHaarMeasure

theorem finiteHaar_integral_pos : 0 < finiteHaar p c (integral p c) :=
  (isOpen_integral p c).measure_pos (finiteHaar p c) (integral_nonempty p c)

theorem finiteHaar_integral_lt_top : finiteHaar p c (integral p c) < ⊤ :=
  (isCompact_integral p c).measure_lt_top

private theorem finiteHaar_integral_toReal_pos :
    0 < (finiteHaar p c (integral p c)).toReal :=
  ENNReal.toReal_pos (finiteHaar_integral_pos p c).ne' (finiteHaar_integral_lt_top p c).ne

theorem isCompact_smul_integral (a : Tensor K (.finite p) c) :
    IsCompact (a • integral p c) := by
  rw [← Set.image_smul]
  exact (isCompact_integral p c).image (continuous_const.mul continuous_id)

theorem measurableSet_smul_integral (a : Tensor K (.finite p) c) :
    MeasurableSet (a • integral p c) :=
  (isCompact_smul_integral p c a).isClosed.measurableSet

theorem finiteHaar_smul_integral_pos {a : Tensor K (.finite p) c} (ha : IsUnit a) :
    0 < finiteHaar p c (a • integral p c) := by
  obtain ⟨a, rfl⟩ := ha
  let e := (ContinuousAddEquiv.mulLeft a).toHomeomorph
  change 0 < finiteHaar p c (e '' integral p c)
  exact (e.isOpenMap _ (isOpen_integral p c)).measure_pos (finiteHaar p c)
    ((integral_nonempty p c).image e)

theorem finiteHaar_smul_integral_lt_top (a : Tensor K (.finite p) c) :
    finiteHaar p c (a • integral p c) < ⊤ :=
  (isCompact_smul_integral p c a).measure_lt_top

/-- The logarithm of the Haar mass relative to the integral closure, divided by the degree. -/
def finiteComponentVol (S : Set (Tensor K (.finite p) c)) : ℝ :=
  Real.log ((finiteHaar p c S).toReal / (finiteHaar p c (integral p c)).toReal) /
    (Module.finrank ℚ_[p] (Tensor K (.finite p) c) : ℝ)

theorem finiteComponentVol_integral : finiteComponentVol p c (integral p c) = 0 := by
  unfold finiteComponentVol
  rw [div_self (finiteHaar_integral_toReal_pos p c).ne', Real.log_one, zero_div]

theorem finiteComponentVol_mono (a b : Tensor K (.finite p) c) (ha : IsUnit a)
    (_hb : IsUnit b) (h : a • integral p c ⊆ b • integral p c) :
    finiteComponentVol p c (a • integral p c) ≤ finiteComponentVol p c (b • integral p c) := by
  unfold finiteComponentVol
  refine div_le_div_of_nonneg_right (Real.log_le_log (div_pos ?_ (finiteHaar_integral_toReal_pos p c))
    (div_le_div_of_nonneg_right ?_ (finiteHaar_integral_toReal_pos p c).le)) (Nat.cast_nonneg _)
  · exact ENNReal.toReal_pos (finiteHaar_smul_integral_pos p c ha).ne'
      (finiteHaar_smul_integral_lt_top p c a).ne
  · exact ENNReal.toReal_mono (finiteHaar_smul_integral_lt_top p c b).ne (measure_mono h)

theorem finiteComponentVol_eq_zero_of_not_isOver (j : ι) (hj : ¬ IsOver K p (c j))
    (S : Set (Tensor K (.finite p) c)) : finiteComponentVol p c S = 0 := by
  have := subsingleton_tensor_of_not_isOver p c j hj
  have hdim : Module.finrank ℚ_[p] (Tensor K (.finite p) c) = 0 :=
    Module.finrank_zero_of_subsingleton
  simp only [finiteComponentVol, hdim, Nat.cast_zero, div_zero]

theorem finrank_tensor_finite_pos (hc : ∀ j, IsOver K p (c j)) :
    0 < Module.finrank ℚ_[p] (Tensor K (.finite p) c) := by
  change 0 < Module.finrank (baseField (.finite p)) (Tensor K (.finite p) c)
  rw [Module.finrank_eq_card_basis (packetBasis (.finite p) c), Fintype.card_pos_iff]
  refine ⟨fun j => ⟨0, ?_⟩⟩
  have := nontrivial_factor p (c j) (hc j)
  exact Module.finrank_pos

theorem finiteHaar_prime_preimage {U : Set (Tensor K (.finite p) c)} (hU : MeasurableSet U) :
    finiteHaar p c ((fun x => ((p : ℕ) : Tensor K (.finite p) c) * x) ⁻¹' U) =
      ((p : ℕ) : ENNReal) ^ Module.finrank ℚ_[p] (Tensor K (.finite p) c) * finiteHaar p c U := by
  have hmul : (fun x : Tensor K (.finite p) c => ((p : ℕ) : Tensor K (.finite p) c) * x) =
      fun x => ((p : ℕ) : ℚ_[p]) • x := by
    funext x
    rw [Algebra.smul_def, map_natCast]
  rw [hmul]
  exact JoshiTeich.Act1Scene1.PadicHaar.measure_preimage_smul_padic (p := (p : ℕ))
    (finiteHaar p c) hU

theorem finiteComponentVol_prime_preimage (hc : ∀ j, IsOver K p (c j))
    {U : Set (Tensor K (.finite p) c)} (hU : MeasurableSet U)
    (hpos : 0 < finiteHaar p c U) (hfin : finiteHaar p c U < ⊤) :
    finiteComponentVol p c ((fun x => ((p : ℕ) : Tensor K (.finite p) c) * x) ⁻¹' U) =
      finiteComponentVol p c U + Real.log (p : ℕ) := by
  have hn : (Module.finrank ℚ_[p] (Tensor K (.finite p) c) : ℝ) ≠ 0 := by
    exact_mod_cast (finrank_tensor_finite_pos p c hc).ne'
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
  have hratio : 0 < (finiteHaar p c U).toReal / (finiteHaar p c (integral p c)).toReal :=
    div_pos (ENNReal.toReal_pos hpos.ne' hfin.ne) (finiteHaar_integral_toReal_pos p c)
  unfold finiteComponentVol
  rw [finiteHaar_prime_preimage p c hU, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, mul_div_assoc, Real.log_mul (pow_ne_zero _ hp.ne') hratio.ne',
    Real.log_pow, add_div, mul_div_cancel_left₀ _ hn, add_comm]

end

end AbcAdaptation.Reference.Iut.LocalConstruct
