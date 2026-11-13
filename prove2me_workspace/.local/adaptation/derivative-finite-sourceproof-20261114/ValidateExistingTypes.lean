import Lean
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalDerivativeBadPlacesFinite
set_option autoImplicit false
open AbcAdaptation
open AbcAdaptation.Tripod.Fermat.Proper

/-- OPEN: source generic finite-generation/localization statement. The
actual derivative with respect to ψ preserves all but finitely many actual
local rings containing ψ. The set ranges over every valuative place of M.K. -/
theorem PlatformTarget_noncriticalDerivativeBadPlacesFinite {N : ℕ} (M : Model N)
    (ψ : M.K) (hψ : Transcendental ℚ ψ) :
    {P : Place M.K | ψ ∈ P.1 ∧
      ∃ s ∈ P.1, CurveDeriv.derivAlong ψ s ∉ P.1}.Finite := by
  sorry

open Lean
run_meta do
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalDerivativeBadPlacesFinite
  let b ← getConstInfo `PlatformTarget_noncriticalDerivativeBadPlacesFinite
  unless ← Lean.Meta.isDefEq a.type b.type do throwError "Platform target differs"
  IO.FS.writeFile ".local/adaptation/derivative-finite-sourceproof-20261114/existing-types-equal.json" "true"
