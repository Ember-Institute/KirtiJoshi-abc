/-
Copyright (c) 2026 The genl contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The genl contributors

Concrete Fermat specialization of the epsilon bookkeeping in
Genl/GeneralPosition/TheoremTwoOne.lean. No open theorem is imported here.
-/
import Definitions.Def_TripodFermatInputs

set_option autoImplicit false

namespace AbcAdaptation.Tripod

theorem statementI_of_fermat_children
    (hNorm : Fermat.HeightNormalization)
    (hLift : Fermat.LiftDifferent)
    (hFermat : Fermat.CanonicalEstimate)
    (hII : StatementII) : StatementI := by
  intro d ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (max 3 (3 * (1 + ε) / ε))
  have hN3R : (3 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN3 : 3 < N := by exact_mod_cast hN3R
  have hNpos : (0 : ℝ) < N := by linarith
  have hNposNat : 0 < N := by omega
  have hNbound : 3 * (1 + ε) < (N : ℝ) * ε := by
    exact (div_lt_iff₀ hε).mp (lt_of_le_of_lt (le_max_right _ _) hN)
  let a : ℝ := Fermat.coefficient N
  have ha : 0 < a := div_pos (by linarith) hNpos
  let δ : ℝ := a * (1 + ε) - 1
  have hδ : 0 < δ := by
    dsimp [δ, a, Fermat.coefficient]
    apply sub_pos.mpr
    rw [div_mul_eq_mul_div, lt_div_iff₀ hNpos]
    nlinarith
  have hδeq : 1 + δ = a * (1 + ε) := by dsimp [δ]; ring
  obtain ⟨CN, hCN⟩ := hNorm N hN3
  obtain ⟨CD, hCD⟩ := hLift N hNposNat
  obtain ⟨CF, hCF⟩ := hFermat hII N hN3 (N ^ 2 * d) δ hδ
  refine ⟨((1 + δ) * CD + CF + CN) / a, ?_⟩
  intro z hzd
  obtain ⟨p, hpz, hpd, hpD⟩ := hCD z
  have hpbound : Fermat.degree p ≤ N ^ 2 * d :=
    hpd.trans (Nat.mul_le_mul_left _ hzd)
  have hcan := hCF p hpbound
  have hnorm := (abs_le.mp (hCN p)).1
  rw [hpz] at hnorm
  have hdiff := mul_le_mul_of_nonneg_left hpD (by linarith : 0 ≤ 1 + δ)
  have hmain : a * htCan z ≤
      a * ((1 + ε) * (logDiff z + logCond z)) +
        ((1 + δ) * CD + CF + CN) := by
    change -CN ≤ Fermat.canonicalHeight p - a * htCan z at hnorm
    rw [hδeq] at hdiff hcan
    nlinarith
  apply (mul_le_mul_iff_right₀ ha).mp
  have hcancel :
      a * ((1 + ε) * (logDiff z + logCond z) +
        ((1 + δ) * CD + CF + CN) / a) =
      a * ((1 + ε) * (logDiff z + logCond z)) +
        ((1 + δ) * CD + CF + CN) := by
    field_simp [ha.ne']
    <;> ring
  rw [hcancel]
  exact hmain

end AbcAdaptation.Tripod
