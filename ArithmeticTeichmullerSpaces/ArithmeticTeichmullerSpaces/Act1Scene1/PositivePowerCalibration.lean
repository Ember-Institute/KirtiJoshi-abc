import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
source-id: JT-SCENE1-POSITIVE-POWER-CALIBRATION
source: Joshi II `se:ff-rings`, scalar normalization of the rho norms
on a Frechet Q_p algebra.
fidelity: a positive logarithmic power takes one contracting real base
to another. Positive powers preserve maxima and detect convergence to
zero of nonnegative functions, with the original filter unchanged.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; actual scalar and seminorm laws are consumers.
-/

namespace JoshiTeich.Act1Scene1.PositivePowerCalibration

open scoped Topology
noncomputable section

def exponent (r s : ℝ) : ℝ := Real.log s / Real.log r

theorem exponent_pos (r s : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s) (hs1 : s < 1) :
    0 < exponent r s := div_pos_of_neg_of_neg (Real.log_neg hs0 hs1) (Real.log_neg hr0 hr1)

theorem rpow_exponent (r s : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s) :
    r ^ exponent r s = s := by
  rw [Real.rpow_def_of_pos hr0, exponent,
    mul_div_cancel₀ (Real.log s) (Real.log_neg hr0 hr1).ne, Real.exp_log hs0]

theorem rpow_max (x y a : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 ≤ a) :
    (max x y) ^ a = max (x ^ a) (y ^ a) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, max_eq_right (Real.rpow_le_rpow hx h ha)]
  · rw [max_eq_left h, max_eq_left (Real.rpow_le_rpow hy h ha)]

theorem tendsto_rpow_zero_iff {ι : Type*} (l : Filter ι) (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun i => f i ^ a) l (𝓝 0) ↔ Filter.Tendsto f l (𝓝 0) := by
  constructor
  · intro h
    have hi := h.rpow_const_nhds_zero (inv_pos.mpr ha)
    simpa only [Real.rpow_rpow_inv (hf _) ha.ne'] using hi
  · exact fun h => h.rpow_const_nhds_zero ha

end
end JoshiTeich.Act1Scene1.PositivePowerCalibration
