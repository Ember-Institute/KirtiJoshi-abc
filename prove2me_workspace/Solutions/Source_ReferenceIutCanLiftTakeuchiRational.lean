/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/S1/Rational.lean, lines 44–184
-/
import Solutions.Source_ReferenceIutCanLiftTakeuchiOrbifoldLocalForm
import Solutions.Source_ReferenceIutCanLiftTakeuchiRatCert
import Mathlib.Analysis.Complex.Polynomial.Basic

set_option autoImplicit false

/-!
# Analytic properties of a certified rational function

The certificate locates the poles, describes the local forms off the poles,
and gives a nonconstant polynomial equation for each finite fiber.
-/

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi.RatCert

open Filter Polynomial Set
open scoped Topology

variable {f N D H K R : ℂ[X]} {c : ℂ}

private theorem eval_ne_of_bezout {P Q : ℂ[X]}
    (h : ∃ a b, ∃ d : ℂ, d ≠ 0 ∧ a * P + b * Q = C d) {x : ℂ}
    (hQ : Q.eval x = 0) : P.eval x ≠ 0 := by
  obtain ⟨a, b, d, hd, h⟩ := h
  intro hP
  have he := congrArg (eval x) h
  simp only [eval_add, eval_mul, hP, hQ, mul_zero, add_zero, eval_C] at he
  exact hd he.symm

private theorem eval_zero_of_dvd {P : ℂ[X]}
    (h : ∃ q, ∃ d : ℂ, d ≠ 0 ∧ C d * f ^ 6 = P * q)
    {x : ℂ} (hP : P.eval x = 0) : f.eval x = 0 := by
  obtain ⟨q, d, hd, h⟩ := h
  have he := congrArg (eval x) h
  simp only [eval_mul, eval_pow, eval_C, hP, zero_mul] at he
  exact (pow_eq_zero_iff (n := 6) (by norm_num)).mp ((mul_eq_zero.mp he).resolve_left hd)

variable (hc : RatCert f N D H K R c)
include hc

theorem D_eval_eq_zero_iff (x : ℂ) : D.eval x = 0 ↔ f.eval x = 0 := by
  refine ⟨eval_zero_of_dvd hc.D_dvd_f, fun h ↦ ?_⟩
  obtain ⟨q, hq⟩ := hc.f_dvd_D
  rw [hq, eval_mul, h, zero_mul]

theorem N_eval_ne {x : ℂ} (hx : f.eval x = 0) : N.eval x ≠ 0 := by
  rw [hc.hN, eval_mul, eval_C, eval_pow]
  exact mul_ne_zero hc.c_ne (pow_ne_zero _ (eval_ne_of_bezout hc.H_cop hx))

private theorem D_eval_ne {x : ℂ} (hx : f.eval x ≠ 0) : D.eval x ≠ 0 :=
  fun hD ↦ hx ((hc.D_eval_eq_zero_iff x).mp hD)

/-- The rational function determined by the certificate. -/
noncomputable def G (_ : RatCert f N D H K R c) (x : ℂ) : ℂ := N.eval x / D.eval x

theorem G_def (x : ℂ) : hc.G x = N.eval x / D.eval x := rfl

theorem differentiableAt {x : ℂ} (hx : f.eval x ≠ 0) : DifferentiableAt ℂ hc.G x :=
  N.differentiableAt.div D.differentiableAt (hc.D_eval_ne hx)

theorem differentiableOn : DifferentiableOn ℂ hc.G {x | f.eval x = 0}ᶜ :=
  fun _ hx ↦ (hc.differentiableAt hx).differentiableWithinAt

theorem analyticAt {x : ℂ} (hx : f.eval x ≠ 0) : AnalyticAt ℂ hc.G x :=
  (N.differentiable.analyticAt x).div (D.differentiable.analyticAt x) (hc.D_eval_ne hx)

theorem G_eq_zero_iff {x : ℂ} (hx : f.eval x ≠ 0) : hc.G x = 0 ↔ H.eval x = 0 := by
  rw [G_def, div_eq_zero_iff, or_iff_left (hc.D_eval_ne hx), hc.hN, eval_mul, eval_C,
    eval_pow, mul_eq_zero, or_iff_right hc.c_ne, pow_eq_zero_iff (by norm_num)]

private theorem G_sub_eq {x : ℂ} (hx : D.eval x ≠ 0) :
    hc.G x - 1728 = c * K.eval x ^ 2 / D.eval x := by
  have he := congrArg (eval x) hc.hK
  simp only [eval_sub, eval_mul, eval_ofNat, eval_C, eval_pow] at he
  rw [G_def, div_sub' hx, mul_comm (D.eval x) 1728, he]

theorem G_eq_1728_iff {x : ℂ} (hx : f.eval x ≠ 0) : hc.G x = 1728 ↔ K.eval x = 0 := by
  have hd := hc.D_eval_ne hx
  rw [← sub_eq_zero, hc.G_sub_eq hd, div_eq_zero_iff, or_iff_left hd, mul_eq_zero,
    or_iff_right hc.c_ne, pow_eq_zero_iff (by norm_num)]

theorem sig_G {x : ℂ} (hx : f.eval x ≠ 0) :
    sig (hc.G x) = if H.eval x = 0 then 3 else if K.eval x = 0 then 2 else 1 := by
  simp only [sig, hc.G_eq_zero_iff hx, hc.G_eq_1728_iff hx]

/-- The certificate gives the local form of the rational function away from its poles. -/
theorem hasLocalForm {x : ℂ} (hx : f.eval x ≠ 0) : HasLocalForm hc.G x (sig (hc.G x)) := by
  have hd := hc.D_eval_ne hx
  have hφ : AnalyticAt ℂ (fun y ↦ c / D.eval y) x :=
    analyticAt_const.div (D.differentiable.analyticAt x) hd
  have hφ0 : c / D.eval x ≠ 0 := div_ne_zero hc.c_ne hd
  rw [hc.sig_G hx]
  split_ifs with hH hK
  · refine hasLocalForm_of_eq_pow_mul (by norm_num) (H.differentiable.analyticAt x) hH
      ?_ hφ hφ0 ?_
    · rw [Polynomial.deriv]
      exact eval_ne_of_bezout hc.H_sqf hH
    · exact Eventually.of_forall fun y ↦ by
        rw [(hc.G_eq_zero_iff hx).mpr hH, zero_add, G_def, hc.hN, eval_mul, eval_C,
          eval_pow, ← mul_div_assoc, mul_comm c]
  · refine hasLocalForm_of_eq_pow_mul (by norm_num) (K.differentiable.analyticAt x) hK
      ?_ hφ hφ0 ?_
    · rw [Polynomial.deriv]
      exact eval_ne_of_bezout hc.K_sqf hK
    · filter_upwards [D.continuous.continuousAt.eventually_ne hd] with y hy
      rw [(hc.G_eq_1728_iff hx).mpr hK, ← sub_eq_iff_eq_add', hc.G_sub_eq hy,
        ← mul_div_assoc, mul_comm c (K.eval y ^ 2)]
  · refine hasLocalForm_one (hc.analyticAt hx) ?_
    have hderiv : HasDerivAt hc.G ((N.derivative.eval x * D.eval x - N.eval x *
        D.derivative.eval x) / D.eval x ^ 2) x :=
      (N.hasDerivAt x).div (D.hasDerivAt x) hd
    have hcrit := congrArg (eval x) hc.hcrit
    simp only [eval_sub, eval_mul, eval_pow] at hcrit
    rw [hderiv.deriv, hcrit]
    have hR : R.eval x ≠ 0 := fun h ↦ hx (eval_zero_of_dvd hc.R_dvd_f h)
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hR (pow_ne_zero _ hH)) hK) (pow_ne_zero _ hd)

private theorem natDegree_sub_C_mul (w : ℂ) : (N - C w * D).natDegree = N.natDegree :=
  natDegree_sub_eq_left_of_natDegree_lt ((natDegree_C_mul_le w D).trans_lt hc.deg)

private theorem natDegree_pos : 0 < N.natDegree :=
  (Nat.zero_le D.natDegree).trans_lt hc.deg

private theorem sub_C_mul_ne_zero (w : ℂ) : N - C w * D ≠ 0 := by
  intro h
  have hdeg := hc.natDegree_sub_C_mul w
  rw [h, natDegree_zero] at hdeg
  exact hc.natDegree_pos.ne hdeg

/-- Every finite fiber off the poles is a subset of a finite polynomial root set. -/
theorem finite_fiber (w : ℂ) : {x | f.eval x ≠ 0 ∧ hc.G x = w}.Finite := by
  refine (Polynomial.finite_setOfPred_isRoot (hc.sub_C_mul_ne_zero w)).subset ?_
  rintro x ⟨hx, hGx⟩
  rw [G_def, div_eq_iff (hc.D_eval_ne hx)] at hGx
  simp only [mem_ofPred_eq, IsRoot, eval_sub, eval_mul, eval_C, hGx, sub_self]

/-- Every finite value is attained away from the poles. -/
theorem surj (w : ℂ) : ∃ x, f.eval x ≠ 0 ∧ hc.G x = w := by
  have hdeg : 0 < degree (N - C w * D) := by
    rw [degree_eq_natDegree (hc.sub_C_mul_ne_zero w), hc.natDegree_sub_C_mul]
    exact_mod_cast hc.natDegree_pos
  obtain ⟨x, hx⟩ := Complex.exists_root hdeg
  simp only [IsRoot, eval_sub, eval_mul, eval_C] at hx
  have hf : f.eval x ≠ 0 := by
    intro h
    rw [(hc.D_eval_eq_zero_iff x).mpr h, mul_zero, sub_zero] at hx
    exact hc.N_eval_ne h hx
  exact ⟨x, hf, (div_eq_iff (hc.D_eval_ne hf)).2 (sub_eq_zero.mp hx)⟩

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi.RatCert
