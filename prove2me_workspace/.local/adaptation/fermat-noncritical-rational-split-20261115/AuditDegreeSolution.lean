import Lean
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalP1DegreeOneRational
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

open Lean
run_meta do
  let actual ← getConstInfo `solution
  let target ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalP1DegreeOneRational
  unless ← Lean.Meta.isDefEq actual.type target.type do throwError "Exact current target type differs"
  let .thmInfo body := actual | throwError "Expected theorem solution"
  let used := body.value.getUsedConstants
  unless !used.contains `AbcAdaptation.Tripod.Fermat.Proper.noncriticalP1DegreeOneRational do throwError "Circular target reference"
  let axs ← collectAxioms `solution
  for ax in axs do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do throwError "Unexpected direct source proof axiom {ax}"
  let result := Json.mkObj [("typeEqualToActualTarget", toJson true), ("circularTargetReference", toJson false), ("axioms", toJson (axs.map toString)), ("usedConstants", toJson (used.map toString)), ("type", toJson (← Lean.Meta.ppExpr actual.type).pretty)]
  IO.FS.writeFile ".local/adaptation/fermat-noncritical-rational-split-20261115/degree-solution-audit.json" (result.pretty ++ "\n")

#print axioms solution
