/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Concrete/LocalConstruct/Integral.lean (norm_le_one_of_ordp_nonneg)
  and Iut/Concrete/LocalConstruct/Prop14.lean (ordp_div_residueChar_pow)
-/
import Solutions.Source_ReferenceIutConcreteLocalArithmetic
import ArithmeticTeichmullerSpaces.Prologue.Arithmetic.Basic

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.LocalConstruct

open NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- A nonnegative normalized order gives an element of the completion's unit ball. -/
lemma norm_le_one_of_ordp_nonneg {w : FinitePlace K} {x : completionAt K w}
    (h : 0 ≤ ordp K w x) : ‖x‖ ≤ 1 := by
  have hp : (1 : ℝ) < residueChar w := by
    exact_mod_cast (Tripod.residueChar_prime w).one_lt
  have hlog : 0 < Real.log (residueChar w) := Real.log_pos hp
  have hn : (0 : ℝ) < localDeg K w := by exact_mod_cast localDeg_pos w
  unfold ordp at h
  have h' : 0 ≤ -Real.log ‖x‖ := by
    have := mul_nonneg h (mul_pos hn hlog).le
    rwa [div_mul_cancel₀ _ (mul_pos hn hlog).ne'] at this
  exact (Real.log_nonpos_iff (norm_nonneg x)).mp (neg_nonneg.mp h')

/-- Dividing by the m-th power of the residue prime subtracts m from the normalized order. -/
lemma ordp_div_residueChar_pow (w : FinitePlace K) (x : completionAt K w) (hx : x ≠ 0)
    (m : ℕ) :
    ordp K w (x / (residueChar w : completionAt K w) ^ m) = ordp K w x - m := by
  have hp0 : (residueChar w : K) ≠ 0 := Nat.cast_ne_zero.mpr (Tripod.residueChar_prime w).ne_zero
  have hℓ : (residueChar w : completionAt K w) ≠ 0 := by
    rw [← map_natCast (algebraMap K (completionAt K w))]
    exact (map_ne_zero _).mpr hp0
  have hpow : (residueChar w : completionAt K w) ^ m ≠ 0 := pow_ne_zero _ hℓ
  have hordPrime : ordp K w (residueChar w : completionAt K w) = 1 := by
    rw [← map_natCast (algebraMap K (completionAt K w))]
    exact ordp_p w
  have hordPow : ordp K w ((residueChar w : completionAt K w) ^ m) = m := by
    have h := JoshiTeich.Prologue.Arithmetic.ordp_pow w (residueChar w : completionAt K w) m
    change ordp K w ((residueChar w : completionAt K w) ^ m) =
      (m : ℝ) * ordp K w (residueChar w : completionAt K w) at h
    rwa [hordPrime, mul_one] at h
  have h := ordp_mul w (x / (residueChar w : completionAt K w) ^ m)
    ((residueChar w : completionAt K w) ^ m) (div_ne_zero hx hpow) hpow
  rw [div_mul_cancel₀ x hpow, hordPow] at h
  exact (eq_sub_iff_add_eq).mpr h.symm

end AbcAdaptation.Reference.Iut.LocalConstruct
