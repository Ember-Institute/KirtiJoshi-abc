/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/M2/Final.lean
-/
import Mathlib.Data.Rat.Cast.CharZero
import Solutions.Source_ReferenceIutCanLiftNielsenDescent
import Solutions.Source_ReferenceIutCanLiftPadicIntegrality

set_option autoImplicit false

open Matrix
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2

open Fricke (tr)
open Takeuchi (TakeuchiSq takeuchi_one_infty_of_int)

/-- If a matrix in `SL(2, ℝ)` is proportional to a rational matrix, its squared trace is
the rational matrix's squared trace divided by its determinant. -/
theorem trace_sq_eq_of_rational_rep {g : SL(2, ℝ)} {c : ℝ} {R : Matrix (Fin 2) (Fin 2) ℚ}
    (hR : (g : Matrix (Fin 2) (Fin 2) ℝ) = c • R.map (Rat.castHom ℝ)) :
    tr g ^ 2 = ((R.trace ^ 2 / R.det : ℚ) : ℝ) := by
  have hdet : c ^ 2 * (R.det : ℝ) = 1 := by
    have h := g.det_coe
    rw [hR, Matrix.det_smul, Fintype.card_fin] at h
    change c ^ 2 * ((Rat.castHom ℝ).mapMatrix R).det = 1 at h
    rw [← (Rat.castHom ℝ).map_det] at h
    exact h
  have hd : (R.det : ℝ) ≠ 0 := by
    intro hzero
    simp [hzero] at hdet
  calc
    tr g ^ 2 = (c * (R.trace : ℝ)) ^ 2 := by
      rw [tr, hR, Matrix.trace_smul, smul_eq_mul,
        ← AddMonoidHom.map_trace (Rat.castHom ℝ) R]
      rfl
    _ = ((R.trace ^ 2 / R.det : ℚ) : ℝ) := by
      have hpow : ((R.trace ^ 2 : ℚ) : ℝ) = (R.trace : ℝ) ^ 2 :=
        (Rat.castHom ℝ).map_pow R.trace 2
      rw [Rat.cast_div, hpow, eq_div_iff hd, mul_pow, mul_right_comm, hdet, one_mul]

/-- The p-adic bounds on the rational representative give an integer squared trace. -/
theorem exists_int_sq_tr_of_padicNorm_le_one {g : SL(2, ℝ)}
    {c : ℝ} {R : Matrix (Fin 2) (Fin 2) ℚ}
    (hR : (g : Matrix (Fin 2) (Fin 2) ℝ) = c • R.map (Rat.castHom ℝ))
    (hbound : ∀ p : ℕ, p.Prime → padicNorm p (R.trace ^ 2 / R.det) ≤ 1) :
    ∃ m : ℤ, tr g ^ 2 = (m : ℝ) := by
  obtain ⟨m, hm⟩ := exists_int_of_padicNorm_le_one hbound
  exact ⟨m, by rw [trace_sq_eq_of_rational_rep hR, hm, Rat.cast_intCast]⟩

/-- The bounds at every prime supply Takeuchi's reduction with integral squared traces
on the generated subgroup. -/
theorem takeuchi_one_infty_of_padicNorm_le_one {A B : SL(2, ℝ)}
    (hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2) (hA : tr A ≠ 0)
    (hrep : ∀ γ ∈ Subgroup.closure {A, B}, ∃ (c : ℝ) (R : Matrix (Fin 2) (Fin 2) ℚ),
      (γ : Matrix (Fin 2) (Fin 2) ℝ) = c • R.map (Rat.castHom ℝ) ∧
      ∀ p : ℕ, p.Prime → padicNorm p (R.trace ^ 2 / R.det) ≤ 1) :
    ∃ A' B' : SL(2, ℝ), Subgroup.closure {A', B'} = Subgroup.closure {A, B} ∧
      tr (A' * B' * A'⁻¹ * B'⁻¹) = -2 ∧ TakeuchiSq (tr A') (tr B') (tr (A' * B')) := by
  apply takeuchi_one_infty_of_int hcomm hA
  intro γ hγ
  obtain ⟨c, R, hR, hbound⟩ := hrep γ hγ
  exact exists_int_sq_tr_of_padicNorm_le_one hR hbound

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2
