import Definitions.Def_FermatInfinityDivisorFiniteSupport
import Definitions.Def_FermatCanonicalCoordinatePoleComposition

set_option autoImplicit false
open scoped IntermediateField

theorem AbcAdaptation.Tripod.Fermat.Proper.coordinatePoleMultiplicity_eq : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M),
  0 < N →
    ∀ (P : AbcAdaptation.Tripod.Fermat.Proper.Place ↥M.K),
      AbcAdaptation.Tripod.Fermat.Proper.poleMultiplicity M hDVR M.u P =
        AbcAdaptation.Tripod.Fermat.Proper.poleMultiplicity M hDVR M.v P := by sorry

set_option pp.fullNames true
set_option pp.funBinderTypes true
open Lean
run_meta do
  let mut rows : Array Json := #[]
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.coordinatePoleMultiplicity_eq
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.coordinatePoleMultiplicity_eq"), ("type", Json.str fmt.pretty)])
  IO.FS.writeFile ".local/adaptation/fermat-canonical-decomposition-20261114/upload-elaborated-types.json" (Json.pretty (Json.arr rows))
