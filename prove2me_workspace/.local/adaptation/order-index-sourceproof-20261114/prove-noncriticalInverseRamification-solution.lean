import Definitions.Def_FermatNoncriticalElementarySource
import Definitions.Def_FermatNoncriticalOrderSource
import Mathlib.Algebra.Polynomial.Reverse
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalPolynomialOrderAtRegularPoint
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open AbcAdaptation
open Polynomial
open AbcAdaptation.Tripod.Fermat.Proper

/-- Complete source `exists_ramIdx_eq_mul_inv`; consumed twice by the unit branch below. -/
private theorem noncritical_exists_ramIdx_eq_mul_inv {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ)
    (x : QbarPoint M.K)
    (h0 : letI : IsCurveField M.K := M.isCurveField; x.P.ord ψ = 0) :
    ∃ k : ℕ, ramIdx M hDVR ψ x.P = ramIdx M hDVR ψ⁻¹ x.P * (k : ℤ) := by
  letI : IsCurveField M.K := M.isCurveField
  have hψ0 : ψ ≠ 0 := ne_zero_of_transcendental hψ
  obtain ⟨h, hinv⟩ := (x.P.ord_eq_zero_iff hψ0).mp h0
  set m := minpoly ℚ (x.P.residue ⟨ψ, h⟩)
  have hm0 : m ≠ 0 := minpoly.ne_zero (x.P.noncritical_isIntegral_residue _)
  letI : Invertible ψ := invertibleOfNonzero hψ0
  have key : aeval ψ⁻¹ m.reverse * ψ ^ m.natDegree = aeval ψ m := by
    have := eval₂_reverse_mul_pow (algebraMap ℚ M.K) ψ m
    rwa [invOf_eq_inv] at this
  have hr0 : m.reverse ≠ 0 := by rwa [Ne, reverse_eq_zero]
  have hne : aeval ψ⁻¹ m.reverse ≠ 0 := fun h0 ↦
    transcendental_inv hψ ⟨_, hr0, h0⟩
  rw [NoncriticalElementarySource.ramIdx_of_mem M hDVR h, ← key, x.P.ord_mul hne (pow_ne_zero _ hψ0), x.P.ord_pow, h0, mul_zero,
    add_zero, noncriticalPolynomialOrderAtRegularPoint M hDVR ψ⁻¹ (transcendental_inv hψ) x hinv hr0]
  exact ⟨_, rfl⟩

theorem solution {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ)
    (x : QbarPoint M.K) :
    ramIdx M hDVR ψ⁻¹ x.P = ramIdx M hDVR ψ x.P := by
  letI : IsCurveField M.K := M.isCurveField
  have hψ0 : ψ ≠ 0 := ne_zero_of_transcendental hψ
  rcases lt_trichotomy (x.P.ord ψ) 0 with hlt | h0 | hgt
  · have hi : 0 < x.P.ord ψ⁻¹ := by rw [x.P.ord_inv]; omega
    have he : ramIdx M hDVR ψ⁻¹ x.P = x.P.ord ψ⁻¹ := by
      simpa only [ord_eq_placeOrd] using
        noncritical_ramIdx_of_positive_order M hDVR ψ⁻¹ x.P
          (by simpa only [ord_eq_placeOrd] using hi)
    rw [he, NoncriticalElementarySource.ramIdx_of_notMem M hDVR
      ((x.P.ord_neg_iff).mp hlt), x.P.ord_inv]
  · obtain ⟨k₁, hk₁⟩ := noncritical_exists_ramIdx_eq_mul_inv M hDVR ψ hψ x h0
    obtain ⟨k₂, hk₂⟩ := noncritical_exists_ramIdx_eq_mul_inv M hDVR ψ⁻¹ (transcendental_inv hψ) x
      (by rw [x.P.ord_inv, h0, neg_zero])
    rw [inv_inv] at hk₂
    have e₁ := noncriticalRamificationPositive M hDVR ψ hψ x.P
    have e₂ := noncriticalRamificationPositive M hDVR ψ⁻¹ (transcendental_inv hψ) x.P
    have hk₁' : (1 : ℤ) ≤ k₁ := by
      rcases Nat.eq_zero_or_pos k₁ with h | h
      · rw [h, Nat.cast_zero, mul_zero] at hk₁; omega
      · exact_mod_cast h
    have hk₂' : (1 : ℤ) ≤ k₂ := by
      rcases Nat.eq_zero_or_pos k₂ with h | h
      · rw [h, Nat.cast_zero, mul_zero] at hk₂; omega
      · exact_mod_cast h
    nlinarith
  · have hi : x.P.ord ψ⁻¹ < 0 := by rw [x.P.ord_inv]; omega
    have he : ramIdx M hDVR ψ x.P = x.P.ord ψ := by
      simpa only [ord_eq_placeOrd] using
        noncritical_ramIdx_of_positive_order M hDVR ψ x.P
          (by simpa only [ord_eq_placeOrd] using hgt)
    rw [NoncriticalElementarySource.ramIdx_of_notMem M hDVR
      ((x.P.ord_neg_iff).mp hi), he, x.P.ord_inv, neg_neg]
