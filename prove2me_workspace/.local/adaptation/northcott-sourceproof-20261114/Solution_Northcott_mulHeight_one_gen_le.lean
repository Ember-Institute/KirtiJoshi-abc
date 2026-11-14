import Definitions.Def_TripodNorthcottInputs

set_option autoImplicit false
open NumberField Polynomial
open scoped Classical
open AbcAdaptation
open AbcAdaptation.Tripod
open AbcAdaptation.Tripod.Northcott

/-- The multiplicative height `exp (logHeight₁ (gen λ))` of a point of degree `≤ d` and height
`htCan ≤ H` is at most `heightBound d H = exp (d · max H 0)`. -/
theorem solution {d : ℕ} {H : ℝ} {x : Pt} (hd : x ∈ ptLE d) (hH : htCan x ≤ H) :
    Height.mulHeight₁ (gen x.1) ≤ heightBound d H := by
  rw [heightBound, ← Real.exp_log (Height.mulHeight₁_pos _),
    ← Height.logHeight₁_eq_log_mulHeight₁]
  apply Real.exp_le_exp.mpr
  rw [← deg_mul_htCan x]
  exact mul_le_mul (by exact_mod_cast hd) (hH.trans (le_max_left _ _)) (htCan_nonneg _)
    (Nat.cast_nonneg _)
