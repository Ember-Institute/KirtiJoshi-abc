import Definitions.Def_FermatNoncriticalP1Reduction
set_option autoImplicit false
open scoped Classical
open AbcAdaptation
open AbcAdaptation.Tripod.Fermat.Proper
open AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1
open Polynomial IntermediateField

theorem solution {x : Tripod.Qbar} (hx : deg x ≤ 1) :
    ∃ q : ℚ, x = q := by
  letI : Algebra.IsAlgebraic ℚ Tripod.Qbar := AlgebraicClosure.isAlgebraic ℚ
  have h1 : 0 < deg x :=
    minpoly.natDegree_pos (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral
  obtain ⟨q, hq⟩ := minpoly.natDegree_eq_one_iff.mp (le_antisymm hx h1)
  exact ⟨q, by rw [← hq, eq_ratCast]⟩
