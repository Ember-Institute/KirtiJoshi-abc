import Definitions.Def_TripodNorthcottInputs

set_option autoImplicit false
open NumberField Polynomial
open scoped Classical
open AbcAdaptation
open AbcAdaptation.Tripod
open AbcAdaptation.Tripod.Northcott

/-- Each conjugate `φ(x)` of an element `x` of a number field `K` is bounded in absolute value
by the multiplicative height `mulHeight₁ x = exp (logHeight₁ x)` of `x`: the contribution
`mult(v) log⁺ |φ x|` of the infinite place `v` of `φ` to `logHeight₁ x` is at least
`log⁺ |φ x| ≥ log |φ x|`. -/
theorem solution {K : Type*} [Field K] [NumberField K] (x : K)
    (φ : K →+* ℂ) : ‖φ x‖ ≤ Height.mulHeight₁ x := by
  have h1 : Real.posLog (InfinitePlace.mk φ x) ≤ Height.logHeight₁ x := by
    rw [logHeight₁_eq]
    have hfin : 0 ≤ ∑ᶠ v : FinitePlace K, Real.posLog (v x) :=
      finsum_nonneg fun _ ↦ Real.posLog_nonneg
    have hinf : Real.posLog (InfinitePlace.mk φ x) ≤
        ∑ v : InfinitePlace K, (v.mult : ℝ) * Real.posLog (v x) :=
      calc Real.posLog (InfinitePlace.mk φ x)
          ≤ ((InfinitePlace.mk φ).mult : ℝ) * Real.posLog (InfinitePlace.mk φ x) :=
            le_mul_of_one_le_left Real.posLog_nonneg InfinitePlace.one_le_mult
        _ ≤ _ := Finset.single_le_sum
            (f := fun v : InfinitePlace K ↦ (v.mult : ℝ) * Real.posLog (v x))
            (fun v _ ↦ mul_nonneg (Nat.cast_nonneg _) Real.posLog_nonneg) (Finset.mem_univ _)
    exact hinf.trans (le_add_of_nonneg_right hfin)
  rw [InfinitePlace.apply, Height.logHeight₁_eq_log_mulHeight₁] at h1
  have h2 : ‖φ x‖ ≤ Real.exp (Real.posLog ‖φ x‖) := by
    rcases eq_or_ne (φ x) 0 with h | h
    · rw [h, norm_zero]
      exact (Real.exp_pos _).le
    · calc ‖φ x‖ = Real.exp (Real.log ‖φ x‖) := (Real.exp_log (norm_pos_iff.mpr h)).symm
        _ ≤ Real.exp (Real.posLog ‖φ x‖) :=
            Real.exp_le_exp.mpr (by rw [Real.posLog_apply]; exact le_max_right _ _)
  calc ‖φ x‖ ≤ Real.exp (Real.posLog ‖φ x‖) := h2
    _ ≤ Real.exp (Real.log (Height.mulHeight₁ x)) := Real.exp_le_exp.mpr h1
    _ = Height.mulHeight₁ x := Real.exp_log (Height.mulHeight₁_pos x)
