/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Concrete/LocalConstruct/Prop14.lean
-/
import Solutions.Source_ReferenceIutConcreteLocalFiniteIndeterminacy
import Solutions.Source_ReferenceIutConcreteLocalHaar
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.LocalConstruct

open NumberField
open scoped BigOperators Pointwise

universe u

noncomputable section

variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K)

private lemma one_le_ramIdxAt (v : Place K) : 1 ≤ ramIdxAt K v := by
  cases v with
  | inl w => exact ramIdx_pos w
  | inr w => exact le_rfl

private lemma ramTerm_nonneg (v : Place K) :
    0 ≤ if (p : ℕ) - 2 < ramIdxAt K v then 3 + Real.log (ramIdxAt K v) else 0 := by
  split
  · have h : (1 : ℝ) ≤ ramIdxAt K v := by exact_mod_cast one_le_ramIdxAt v
    exact add_nonneg (Nat.cast_nonneg 3) (Real.log_nonneg h)
  · exact le_rfl

private lemma isUnit_natCast_prime : IsUnit ((p : ℕ) : Tensor K (.finite p) c) := by
  rw [← map_natCast (algebraMap ℚ_[p] (Tensor K (.finite p) c))]
  exact (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr p.2.ne_zero)).map _

private lemma preimage_mul_prime_pow_succ_smul_integral (m : ℕ) :
    (fun x => ((p : ℕ) : Tensor K (.finite p) c) * x) ⁻¹'
        (((p : ℕ) : Tensor K (.finite p) c) ^ (m + 1) • integral p c) =
      ((p : ℕ) : Tensor K (.finite p) c) ^ m • integral p c := by
  ext x
  simp only [Set.mem_preimage, Set.mem_smul_set, smul_eq_mul]
  constructor
  · rintro ⟨y, hy, hxy⟩
    rw [pow_succ', mul_assoc] at hxy
    exact ⟨y, hy, (isUnit_natCast_prime p c).mul_left_cancel hxy⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by rw [pow_succ', mul_assoc]⟩

/-- Scaling the integral closure by the m-th power of p subtracts m log p from its log-volume. -/
private theorem finiteComponentVol_prime_pow_smul_integral (hc : ∀ j, IsOver K p (c j))
    (m : ℕ) :
    finiteComponentVol p c (((p : ℕ) : Tensor K (.finite p) c) ^ m • integral p c) =
      -(m : ℝ) * Real.log (p : ℕ) := by
  induction m with
  | zero =>
    rw [pow_zero, one_smul, Nat.cast_zero, neg_zero, zero_mul]
    exact finiteComponentVol_integral p c
  | succ m ih =>
    have hunit := (isUnit_natCast_prime p c).pow (m + 1)
    have h := finiteComponentVol_prime_preimage p c hc
      (measurableSet_smul_integral p c _)
      (finiteHaar_smul_integral_pos p c hunit)
      (finiteHaar_smul_integral_lt_top p c _)
    rw [preimage_mul_prime_pow_succ_smul_integral p c m, ih] at h
    calc
      _ = -(m : ℝ) * Real.log (p : ℕ) - Real.log (p : ℕ) :=
        (eq_sub_iff_add_eq).mpr h.symm
      _ = _ := by rw [Nat.cast_succ, neg_add, add_mul, neg_one_mul, sub_eq_add_neg]

private theorem indAut_image_smul_integral_subset (j : ι) (w : FinitePlace K)
    (h : c j = Place.finite w) (x : completionAt K w) (n m : ℕ)
    (hn : (n : completionAt K w) ^ m ≠ 0) (hx : ‖x / (n : completionAt K w) ^ m‖ ≤ 1)
    {φ : Tensor K (.finite p) c → Tensor K (.finite p) c} (hφ : φ ∈ finiteIndAut p c) :
    φ '' (incl p c j w h x • integral p c) ⊆ (n : Tensor K (.finite p) c) ^ m • integral p c := by
  obtain ⟨σ, hσ⟩ := finiteIndAut_exists_algEquiv p c hφ
  have hIntegral := prop14_iv p c φ hφ
  rw [hσ] at hIntegral ⊢
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  let f := incl p c j w h
  let q := x / (n : completionAt K w) ^ m
  have hq : f q ∈ integral p c := incl_mem_integral p c j w h q hx
  refine ⟨σ (f q * y), hIntegral ⟨_, mul_mem_integral p c hq hy, rfl⟩, ?_⟩
  change (n : Tensor K (.finite p) c) ^ m * σ (f q * y) = σ (f x * y)
  have hPrime : f ((n : completionAt K w) ^ m) = (n : Tensor K (.finite p) c) ^ m := by
    rw [map_pow, map_natCast]
  have hMul : (n : completionAt K w) ^ m * q = x := mul_div_cancel₀ x hn
  calc
    _ = σ ((n : Tensor K (.finite p) c) ^ m * (f q * y)) := by
      simp only [map_mul, map_pow, map_natCast]
    _ = _ := by rw [← hPrime, ← mul_assoc, ← map_mul f, hMul]

/-- IUT IV, Proposition 1.4(iii) in the concrete integral-closure formulation.
A common container is the integral closure scaled by `p ^ ⌊ord_p(x)⌋₊`. -/
theorem prop14iii_of_isOver (hc : ∀ j, IsOver K p (c j)) (d : ι → ℝ) (j : ι)
    (w : FinitePlace K) (h : c j = Place.finite w) (x : completionAt K w) (hx : x ≠ 0)
    (hord : 0 ≤ ordp K w x)
    (hd : ∀ i w', c i = Place.finite w' → d i = differentExponent K w') :
    ∃ a : Tensor K (.finite p) c, IsUnit a ∧
      (∀ φ ∈ finiteIndAut p c,
        φ '' (incl p c j w h x • integral p c) ⊆ a • integral p c) ∧
      finiteComponentVol p c (a • integral p c) ≤
        (-ordp K w x + (∑ i, d i) + 1) * Real.log (p : ℕ) +
          ∑ i, if (p : ℕ) - 2 < ramIdxAt K (c i) then
            3 + Real.log (ramIdxAt K (c i)) else 0 := by
  have hw := hc j
  rw [h, isOver_finite_iff] at hw
  let m : ℕ := ⌊ordp K w x⌋₊
  refine ⟨((p : ℕ) : Tensor K (.finite p) c) ^ m, (isUnit_natCast_prime p c).pow m, ?_, ?_⟩
  · intro φ hφ
    have hn : ((p : ℕ) : completionAt K w) ^ m ≠ 0 := by
      rw [← map_natCast (algebraMap K (completionAt K w))]
      exact pow_ne_zero _ ((map_ne_zero _).mpr (Nat.cast_ne_zero.mpr p.2.ne_zero))
    refine indAut_image_smul_integral_subset p c j w h x p m hn ?_ hφ
    refine norm_le_one_of_ordp_nonneg ?_
    rw [← hw, ordp_div_residueChar_pow w x hx, sub_nonneg]
    exact Nat.floor_le hord
  · rw [finiteComponentVol_prime_pow_smul_integral p c hc]
    have hlogp : 0 ≤ Real.log (p : ℕ) := Real.log_nonneg (by exact_mod_cast p.2.one_lt.le)
    have hm1 : ordp K w x < (m : ℝ) + 1 := Nat.lt_floor_add_one _
    have hd0 : 0 ≤ ∑ i, d i := Finset.sum_nonneg fun i _ => by
      obtain ⟨w', hw', -⟩ := hc i
      rw [hd i w' hw']
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hs0 : 0 ≤ ∑ i, if (p : ℕ) - 2 < ramIdxAt K (c i) then
        3 + Real.log (ramIdxAt K (c i)) else 0 :=
      Finset.sum_nonneg fun i _ => ramTerm_nonneg p (c i)
    have hfloor : -(m : ℝ) ≤ -ordp K w x + 1 := by
      have h' := add_le_add_left (neg_le_neg hm1.le) (1 : ℝ)
      rwa [neg_add, add_assoc, neg_add_cancel, add_zero] at h'
    have hbound : -(m : ℝ) ≤ -ordp K w x + (∑ i, d i) + 1 :=
      hfloor.trans (add_le_add_left (le_add_of_nonneg_right hd0) 1)
    exact (mul_le_mul_of_nonneg_right hbound hlogp).trans (le_add_of_nonneg_right hs0)

end

end AbcAdaptation.Reference.Iut.LocalConstruct
