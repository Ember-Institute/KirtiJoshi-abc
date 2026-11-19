import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

open Bornology Metric Polynomial Set

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

private theorem exists_polynomial_antiderivative (p : ℂ[X]) :
    ∃ q : ℂ[X], q.derivative = p := by
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ h₁ h₂ =>
    obtain ⟨q₁, hq₁⟩ := h₁
    obtain ⟨q₂, hq₂⟩ := h₂
    exact ⟨q₁ + q₂, by rw [derivative_add, hq₁, hq₂]⟩
  | monomial n a =>
    have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    exact ⟨monomial (n + 1) (a / ((n : ℂ) + 1)), by
      rw [derivative_monomial_succ, div_mul_cancel₀ _ hn]⟩

/-- An entire function bounded by a fixed power of twice the unit radius plus the
norm is a polynomial. Cauchy's estimate lowers the growth degree after differentiation. -/
theorem exists_polynomial_of_entire_growth (N : ℕ) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z, ‖f z‖ ≤ C * (2 + ‖z‖) ^ N) :
    ∃ p : ℂ[X], ∀ z, p.eval z = f z := by
  induction N generalizing f C with
  | zero =>
    have hBounded : IsBounded (range f) :=
      isBounded_iff_forall_norm_le.mpr ⟨C, by
        rintro _ ⟨z, rfl⟩
        simpa using hb z⟩
    obtain ⟨c, hc⟩ := hf.exists_const_forall_eq_of_bounded hBounded
    exact ⟨Polynomial.C c, fun z ↦ (eval_C.trans (hc z).symm)⟩
  | succ N ih =>
    have hderiv (z : ℂ) : ‖deriv f z‖ ≤ (C * 2 ^ (N + 1)) * (2 + ‖z‖) ^ N := by
      let R := 2 + ‖z‖
      have hR : 0 < R := by dsimp [R]; positivity
      have hball (w : ℂ) (hw : w ∈ sphere z R) :
          ‖f w‖ ≤ C * (2 * R) ^ (N + 1) := by
        have hnorm : ‖w‖ ≤ R + ‖z‖ := by
          calc
            ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
            _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
            _ = R + ‖z‖ := by rw [mem_sphere_iff_norm.mp hw]
        have hscale : 2 + ‖w‖ ≤ 2 * R := by dsimp [R] at *; linarith
        exact (hb w).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity : 0 ≤ 2 + ‖w‖) hscale (N + 1)) hC)
      calc
        ‖deriv f z‖ ≤ (C * (2 * R) ^ (N + 1)) / R :=
          Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hf.diffContOnCl hball
        _ = (C * 2 ^ (N + 1)) * R ^ N := by
          rw [mul_pow, pow_succ' R, ← mul_assoc, mul_left_comm (C * 2 ^ (N + 1)) R,
            mul_div_cancel_left₀ _ hR.ne']
    obtain ⟨p, hp⟩ := ih hf.deriv (C := C * 2 ^ (N + 1)) (by positivity) hderiv
    obtain ⟨q, hq⟩ := exists_polynomial_antiderivative p
    let g : ℂ → ℂ := fun z ↦ f z - q.eval z
    have hgz (z : ℂ) : HasDerivAt g 0 z := by
      have := (hf z).hasDerivAt.sub (q.hasDerivAt z)
      rwa [hq, hp z, sub_self] at this
    have hconst (z : ℂ) : g z = g 0 :=
      is_const_of_deriv_eq_zero (fun x ↦ (hgz x).differentiableAt)
        (fun x ↦ (hgz x).deriv) z 0
    refine ⟨Polynomial.C (g 0) + q, fun z ↦ ?_⟩
    rw [eval_add, eval_C, ← hconst z]
    exact sub_add_cancel _ _

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
