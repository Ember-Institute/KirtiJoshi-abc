import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
source-id: JT-SCENE1-GEOMETRIC-INTERPOLATION
source: Joshi II `se:ff-rings`, geometric interpolation of rho-weighted
Teichmuller terms in the period-ring norms.
fidelity: constructs positive geometric weights between positive real
endpoints. A Laurent monomial with positive coefficient interpolates
exactly with these weights, including negative integer exponents.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; actual Witt suprema and completion consumers
must establish their own endpoint bounds.
-/

namespace JoshiTeich.Act1Scene1.GeometricInterpolation

noncomputable section

theorem exists_weights (a r b : ℝ) (ha0 : 0 < a) (har : a < r) (hrb : r < b) :
    ∃ u v : ℝ, 0 < u ∧ 0 < v ∧ u + v = 1 ∧ r = a ^ u * b ^ v := by
  have hr0 := ha0.trans har
  have hb0 := hr0.trans hrb
  let d := Real.log b - Real.log a
  have hd : 0 < d := sub_pos.mpr (Real.log_lt_log ha0 (har.trans hrb))
  let u := (Real.log b - Real.log r) / d
  let v := (Real.log r - Real.log a) / d
  have hsum : u + v = 1 := by
    dsimp only [u, v]
    rw [← add_div]
    have hn : (Real.log b - Real.log r) + (Real.log r - Real.log a) = d := by dsimp [d]; ring
    rw [hn, div_self hd.ne']
  have hlog : Real.log a * u + Real.log b * v = Real.log r := by
    dsimp only [u, v]
    field_simp [hd.ne']
    dsimp only [d]
    ring
  refine ⟨u, v, div_pos (sub_pos.mpr (Real.log_lt_log hr0 hrb)) hd,
    div_pos (sub_pos.mpr (Real.log_lt_log ha0 har)) hd, hsum, ?_⟩
  rw [Real.rpow_def_of_pos ha0, Real.rpow_def_of_pos hb0, ← Real.exp_add, hlog, Real.exp_log hr0]

theorem powerRatio_eq_zpow (r : ℝ) (hr : 0 < r) (i m : ℕ) :
    r ^ i / r ^ m = r ^ ((i : ℤ) - (m : ℤ)) := by
  rw [zpow_sub₀ hr.ne', zpow_natCast, zpow_natCast]

theorem monomial_interpolation (a r b c u v : ℝ) (k : ℤ)
    (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c)
    (huv : u + v = 1) (hr : r = a ^ u * b ^ v) :
    c * r ^ k = (c * a ^ k) ^ u * (c * b ^ k) ^ v := by
  calc
    _ = (c ^ u * c ^ v) * ((a ^ k) ^ u * (b ^ k) ^ v) := by
      rw [← Real.rpow_add hc0 u v, huv, Real.rpow_one, hr, mul_zpow,
        Real.rpow_zpow_comm ha0.le, Real.rpow_zpow_comm hb0.le]
    _ = _ := by
      rw [Real.mul_rpow hc0.le (zpow_nonneg ha0.le _),
        Real.mul_rpow hc0.le (zpow_nonneg hb0.le _)]
      ring

end
end JoshiTeich.Act1Scene1.GeometricInterpolation
