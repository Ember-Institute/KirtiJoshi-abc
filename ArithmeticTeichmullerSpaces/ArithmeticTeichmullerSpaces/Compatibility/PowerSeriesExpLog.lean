/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Source: Mathlib/RingTheory/PowerSeries/Log.lean and Substitution.lean,
commit 389347a7c1cfa76f6bd5be2ca35d4cb621610ad3.
Adaptation: specialize the exp/log inverse proofs to rational coefficients
and the derivative API of Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
Consumer: Act1Scene1/AdicExponential.lean. No additional assumptions.
-/
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.WellKnown

namespace JoshiTeich.Compatibility.PowerSeriesExpLog

open PowerSeries
noncomputable section

private theorem derivative_log_mul :
    derivative ℚ (log ℚ) * (1 + X) = 1 := by
  rw [deriv_log]
  change (mk fun n => (-1 : ℚ) ^ n) * (1 + X) = 1
  have h := congrArg (rescale (-1 : ℚ)) (mk_one_mul_one_sub_eq_one ℚ)
  simpa [rescale_mk, rescale_neg_one_X, sub_neg_eq_add] using h

private theorem eq_of_derivative_mul {g : PowerSeries ℚ}
    (hderiv : derivative ℚ g * (1 + X) = g) :
    g = constantCoeff g • (1 + X) := by
  have : Invertible (1 + X : PowerSeries ℚ) :=
    (isUnit_iff_constantCoeff.mpr (by simp)).invertible
  have hcu : constantCoeff (⅟(1 + X) : PowerSeries ℚ) = 1 := by
    have h := congrArg (constantCoeff (R := ℚ)) (mul_invOf_self (1 + X : PowerSeries ℚ))
    rw [map_mul] at h
    simpa using h
  have hg : g * ⅟(1 + X) = derivative ℚ g := by
    conv_lhs => rw [← hderiv]
    rw [mul_assoc, mul_invOf_self, mul_one]
  have key : g * ⅟(1 + X) = C (constantCoeff g) := by
    refine derivative.ext ?_ ?_
    · simp only [Derivation.leibniz, derivative_invOf, map_add, derivative_one,
        derivative_X, zero_add, derivative_C, mul_one, smul_eq_mul, ← hg]
      ring
    · simp [hcu]
  rw [smul_eq_C_mul, ← key, mul_assoc, invOf_mul_self, mul_one]

theorem subst_exp_log : (exp ℚ).subst (log ℚ) = 1 + X := by
  have hderiv : derivative ℚ ((exp ℚ).subst (log ℚ)) * (1 + X) =
      (exp ℚ).subst (log ℚ) := by
    rw [derivative_subst HasSubst.log, derivative_exp, mul_assoc,
      derivative_log_mul, mul_one]
  have hconst : constantCoeff ((exp ℚ).subst (log ℚ)) = 1 := by
    rw [constantCoeff_eq, constantCoeff_subst HasSubst.log,
      finsum_eq_single _ 0 (fun d hd => by
        rw [map_pow, ← constantCoeff_eq, constantCoeff_log, zero_pow hd, smul_zero])]
    simp [constantCoeff_exp]
  have h := eq_of_derivative_mul hderiv
  rwa [hconst, one_smul] at h

theorem subst_log_exp_sub_one : (log ℚ).subst (exp ℚ - 1) = X := by
  let P : PowerSeries ℚ := exp ℚ - 1
  have hp : constantCoeff P = 0 := by simp [P, constantCoeff_exp]
  have hunit : IsUnit (coeff 1 P) := by simp [P, coeff_exp]
  have hPQ : P.subst (log ℚ) = X := by
    rw [subst_sub HasSubst.log, subst_exp_log,
      ← coe_substAlgHom HasSubst.log (R := ℚ), map_one]
    ring
  have hQ : log ℚ = P.substInvOfIsUnit hunit := calc
    _ = PowerSeries.subst (log ℚ) X := (subst_X HasSubst.log).symm
    _ = _ := by
      rw [← P.subst_substInvOfIsUnit_left hp hunit,
        subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hp) HasSubst.log,
        hPQ, X_subst]
  rw [hQ]
  exact P.subst_substInvOfIsUnit_left hp hunit

end
end JoshiTeich.Compatibility.PowerSeriesExpLog
