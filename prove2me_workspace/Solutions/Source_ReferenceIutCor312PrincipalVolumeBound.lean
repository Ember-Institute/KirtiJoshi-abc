import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.ThetaLocalData

/-- Bound the q-pilot logarithm uniformly over procession lengths of at least three. -/
theorem logQ_le_of_globalVolume_bound {n H : ℝ} (hn : 3 ≤ n)
    (hvolume : (n - 1) * (2 * n + 5) * H ≤
      6 * (2 * n + 1) * (n + 3) * Real.log Real.pi) :
    H ≤ (126 / 11) * Real.log Real.pi := by
  have hfactor : 0 < (n - 1) * (2 * n + 5) :=
    mul_pos (by linarith) (by linarith)
  have hgap : 0 ≤ (n - 3) * ((120 * n + 276) / 11) :=
    mul_nonneg (sub_nonneg.mpr hn) (by linarith)
  have hcoeff :
      6 * (2 * n + 1) * (n + 3) ≤ (n - 1) * (2 * n + 5) * (126 / 11) := by
    nlinarith only [hgap]
  have hlog : 0 ≤ Real.log Real.pi :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  apply le_of_mul_le_mul_left _ hfactor
  calc
    (n - 1) * (2 * n + 5) * H ≤ 6 * (2 * n + 1) * (n + 3) * Real.log Real.pi := hvolume
    _ ≤ ((n - 1) * (2 * n + 5) * (126 / 11)) * Real.log Real.pi :=
      mul_le_mul_of_nonneg_right hcoeff hlog
    _ = (n - 1) * (2 * n + 5) * ((126 / 11) * Real.log Real.pi) := mul_assoc _ _ _

end AbcAdaptation.Reference.Iut.ThetaLocalData
