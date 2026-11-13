import Definitions.Def_FermatNoncriticalRamificationPositive

set_option autoImplicit false
open scoped IntermediateField
open AbcAdaptation.Tripod.Fermat.Proper

/-- OPEN: the actual single-elementary-map composition step from the source.
The map is a rational Möbius transformation with nonzero determinant or a
positive-degree rational polynomial. Every actual residue embedding is kept. -/
theorem AbcAdaptation.Tripod.Fermat.Proper.noncriticalElementaryCompositionRamification {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ)
    (x : QbarPoint M.K) (h : NoncriticalP1.ElemMap) :
    Transcendental ℚ (NoncriticalP1.applyK h ψ) ∧
    noncriticalValue M x (NoncriticalP1.applyK h ψ) = h.apply (noncriticalValue M x ψ) ∧
    ramIdx M hDVR (NoncriticalP1.applyK h ψ) x.P =
      ramIdx M hDVR ψ x.P * (h.ramIdx (noncriticalValue M x ψ) : ℤ) := by
  sorry

set_option pp.fullNames true
set_option pp.funBinderTypes true
open Lean
run_meta do
  let mut rows : Array Json := #[]
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalElementaryCompositionRamification
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.noncriticalElementaryCompositionRamification"), ("type", Json.str fmt.pretty)])
  IO.FS.writeFile ".local/adaptation/fermat-noncritical-composition-20261114/upload-elaborated-types.json" (Json.pretty (Json.arr rows))
