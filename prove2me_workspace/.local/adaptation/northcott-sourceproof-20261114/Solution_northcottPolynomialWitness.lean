import Definitions.Def_TripodNorthcottInputs
import Theorems.Thm_AbcAdaptation_Tripod_Northcott_norm_embedding_le_mulHeight_one
import Theorems.Thm_AbcAdaptation_Tripod_Northcott_mulHeight_one_gen_le
import Theorems.Thm_AbcAdaptation_Tripod_Northcott_coeff_minpoly_int_mem_Icc

set_option autoImplicit false
open NumberField Polynomial
open scoped Classical
open AbcAdaptation
open AbcAdaptation.Tripod
open AbcAdaptation.Tripod.Northcott

/-- Source proof of `Iut.Tripod.exists_nat_mem_polySet` (line 157).
The denominator and minpoly are constructed in the actual field `ℚ(x.1)`;
the conjugate estimate is universal over its complex embeddings. -/
theorem solution : Northcott.PolynomialWitness := by
  intro d H x hd hH
  have hmul := mulHeight_one_gen_le hd hH
  have hB₀_pos := heightBound_pos d H
  obtain ⟨n, hn0, hnle, hint⟩ := exists_nat_le_mulHeight₁ (gen x.1)
  have hnB : (n : ℝ) ≤ heightBound d H := hnle.trans hmul
  have hd' : Module.finrank ℚ (fieldOf x.1) ≤ d := by
    rw [← deg_eq_finrank]
    exact hd
  have hconj : ∀ φ : fieldOf x.1 →+* ℂ,
      ‖φ ((n : fieldOf x.1) * gen x.1)‖ ≤ heightBound d H * heightBound d H := by
    intro φ
    rw [map_mul, norm_mul, map_natCast, Complex.norm_natCast]
    exact mul_le_mul hnB ((norm_embedding_le_mulHeight_one _ φ).trans hmul) (norm_nonneg _)
      hB₀_pos.le
  refine ⟨n, hn0, hnB, _, ⟨(natDegree_minpoly_int_le hint).trans hd',
    coeff_minpoly_int_mem_Icc hint hd' hconj⟩, minpoly.monic hint, ?_⟩
  -- `nλ` is a root of its minimal polynomial
  have hy : (n : Qbar) * x.1 = algebraMap (fieldOf x.1) Qbar ((n : fieldOf x.1) * gen x.1) := by
    simp
  rw [hy]
  exact eval₂_minpoly_int_algebraMap _ Qbar
