/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/S1/Main.lean, lines 33–80
-/
import Solutions.Source_ReferenceIutCanLiftPresentation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
# The four elliptic curves in the Takeuchi classification

The rational Weierstrass models give distinct exceptional `j`-invariants.
Their complex base changes are fixed by complex conjugation.
-/

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi

open WeierstrassCurve

/-- The four models over `ℚ` have equations `y² = x(x² + 44x − 16)`,
`y² = (x − 24)(x + 8)(x + 12)`, `y² = x(x² − 16)` and `y² = x³ − 1728`. -/
def qcurve : Fin 4 → WeierstrassCurve ℚ
  | 0 => ⟨0, 44, 0, -16, 0⟩
  | 1 => ⟨0, -4, 0, -384, -2304⟩
  | 2 => ⟨0, 0, 0, -16, 0⟩
  | 3 => ⟨0, 0, 0, 0, -1728⟩

/-- The four rational `j`-invariants in model order. -/
def qj : Fin 4 → ℚ
  | 0 => 488095744 / 125
  | 1 => 1556068 / 81
  | 2 => 1728
  | 3 => 0

instance (k : Fin 4) : (qcurve k).IsElliptic := by
  refine ⟨?_⟩
  rw [isUnit_iff_ne_zero]
  fin_cases k <;> norm_num [qcurve, Δ, b₂, b₄, b₆, b₈]

theorem qcurve_j (k : Fin 4) : (qcurve k).j = qj k := by
  fin_cases k <;> norm_num [j, qcurve, qj, Δ, c₄, b₂, b₄, b₆, b₈]

theorem qj_mem (k : Fin 4) : qj k ∈ canLiftExceptionalJ := by
  fin_cases k <;> simp [qj, canLiftExceptionalJ]

theorem qj_injective : Function.Injective qj := by
  intro k l h
  fin_cases k <;> fin_cases l <;> first | rfl | norm_num [qj] at h

/-- The complex base changes of the four rational models. -/
noncomputable def ccurve (k : Fin 4) : WeierstrassCurve ℂ :=
  (qcurve k).map (algebraMap ℚ ℂ)

instance (k : Fin 4) : (ccurve k).IsElliptic := by
  unfold ccurve
  infer_instance

theorem ccurve_j (k : Fin 4) : (ccurve k).j = (qj k : ℂ) := by
  unfold ccurve
  rw [map_j, qcurve_j]
  simp

theorem ccurve_conj (k : Fin 4) : (ccurve k).map (starRingEnd ℂ) = ccurve k := by
  unfold ccurve
  rw [map_map]
  exact congrArg (qcurve k).map (RingHom.ext_rat _ _)

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi
