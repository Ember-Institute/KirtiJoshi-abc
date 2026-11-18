/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

-/
import Solutions.Source_TripodRelativeDegreeTower

namespace AbcAdaptation.Tripod
open AbcAdaptation.Reference.Iut
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- **`|y|_w = |y|_v^{e(w/v) f(w/v)}`** for `y ∈ k` and `w ∣ v`. -/
lemma apply_algebraMap_eq_pow {w : FinitePlace K} {v : FinitePlace k}
    (hwv : FinitePlace.LiesOver w v) (y : k) :
    w (algebraMap k K y) = v y ^ relLocalDeg w v := by
  by_cases hy : y = 0
  · subst hy
    rw [map_zero, map_zero, map_zero, zero_pow (relLocalDeg_ne_zero hwv)]
  have hy' : algebraMap k K y ≠ 0 := (map_ne_zero _).mpr hy
  have hpos : 0 < w (algebraMap k K y) := FinitePlace.pos_iff.mpr hy'
  have hpos' : 0 < v y := FinitePlace.pos_iff.mpr hy
  have hlog : Real.log (w (algebraMap k K y)) = relLocalDeg w v * Real.log (v y) := by
    rw [AbcAdaptation.Tripod.log_apply_eq w hy', AbcAdaptation.Tripod.log_apply_eq v hy,
      valuation_algebraMap_eq_pow hwv, log_pow, inertDeg_eq_mul hwv,
      residueChar_eq_of_liesOver hwv]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  rw [← Real.exp_log hpos, hlog, ← Real.log_pow, Real.exp_log (pow_pos hpos' _)]

/-- `log⁺|y|_w = e(w/v) f(w/v) · log⁺|y|_v` for `y ∈ k` and `w ∣ v`. -/
lemma posLog_apply_algebraMap_eq {w : FinitePlace K} {v : FinitePlace k}
    (hwv : FinitePlace.LiesOver w v) (y : k) :
    log⁺ (w (algebraMap k K y)) = relLocalDeg w v * log⁺ (v y) := by
  rw [apply_algebraMap_eq_pow hwv, Real.posLog_pow]

end AbcAdaptation.Tripod
