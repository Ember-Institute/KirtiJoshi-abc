import Definitions.Def_FermatProperCarrier
import Definitions.Def_FermatCurveDerivationEtale
import Definitions.Def_FermatCurveDerivationPolynomial
import Definitions.Def_FermatCurveDerivationBasic

set_option autoImplicit false
open scoped IntermediateField
open AbcAdaptation.Tripod.Fermat.Proper

/-- OPEN: source local obstruction. At a regular ramified place, the
actual derivative with respect to ψ fails to preserve the actual local ring.
Both local rings and ramification indices are those of the existing model;
no derivation or derivation law is supplied as a hypothesis. -/
theorem AbcAdaptation.Tripod.Fermat.Proper.noncriticalRegularRamifiedDerivNotMem {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ)
    (P : Place M.K) (hψP : ψ ∈ P.1) (hram : 1 < ramIdx M hDVR ψ P) :
    ∃ s ∈ P.1, CurveDeriv.derivAlong ψ s ∉ P.1 := by
  sorry

/-- OPEN: source generic finite-generation/localization statement. The
actual derivative with respect to ψ preserves all but finitely many actual
local rings containing ψ. The set ranges over every valuative place of M.K. -/
theorem AbcAdaptation.Tripod.Fermat.Proper.noncriticalDerivativeBadPlacesFinite {N : ℕ} (M : Model N)
    (ψ : M.K) (hψ : Transcendental ℚ ψ) :
    {P : Place M.K | ψ ∈ P.1 ∧
      ∃ s ∈ P.1, CurveDeriv.derivAlong ψ s ∉ P.1}.Finite := by
  sorry

set_option pp.fullNames true
set_option pp.funBinderTypes true
open Lean
run_meta do
  let mut rows : Array Json := #[]
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalRegularRamifiedDerivNotMem
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.noncriticalRegularRamifiedDerivNotMem"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalDerivativeBadPlacesFinite
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.noncriticalDerivativeBadPlacesFinite"), ("type", Json.str fmt.pretty)])
  IO.FS.writeFile ".local/adaptation/fermat-noncritical-finite-20261114/upload-elaborated-types.json" (Json.pretty (Json.arr rows))
