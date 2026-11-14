import Lean
import Solutions.Sol_CanonicalLegendreHeightComparison
import Theorems.Thm_AbcAdaptation_Tripod_canonicalLegendreHeightComparison

set_option autoImplicit false
set_option pp.fullNames true
set_option pp.funBinderTypes true

theorem PlatformAudit_legendreFiniteUpperBound : AbcAdaptation.Tripod.LegendreFiniteUpperBound := AbcAdaptation.Tripod.legendreFiniteUpperBound
theorem PlatformAudit_legendreFiniteLowerBound : AbcAdaptation.Tripod.LegendreFiniteLowerBound := AbcAdaptation.Tripod.legendreFiniteLowerBound
theorem PlatformAudit_legendreArchimedeanTripleBound : AbcAdaptation.Tripod.LegendreArchimedeanTripleBound := AbcAdaptation.Tripod.legendreArchimedeanTripleBound
theorem PlatformAudit_legendreZeroJRootOfUnity : AbcAdaptation.Tripod.LegendreZeroJRootOfUnity := AbcAdaptation.Tripod.legendreZeroJRootOfUnity

open Lean
run_meta do
  let mut rows : Array Json := #[]
  let a ← getConstInfo `AbcAdaptation.Tripod.legendreFiniteUpperBound
  let t ← getConstInfo `PlatformAudit_legendreFiniteUpperBound
  unless ← Lean.Meta.isDefEq a.type t.type do throwError "New published type differs: legendreFiniteUpperBound"
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.legendreFiniteUpperBound"), ("type", Json.str (← Lean.Meta.ppExpr a.type).pretty)])
  let a ← getConstInfo `AbcAdaptation.Tripod.legendreFiniteLowerBound
  let t ← getConstInfo `PlatformAudit_legendreFiniteLowerBound
  unless ← Lean.Meta.isDefEq a.type t.type do throwError "New published type differs: legendreFiniteLowerBound"
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.legendreFiniteLowerBound"), ("type", Json.str (← Lean.Meta.ppExpr a.type).pretty)])
  let a ← getConstInfo `AbcAdaptation.Tripod.legendreArchimedeanTripleBound
  let t ← getConstInfo `PlatformAudit_legendreArchimedeanTripleBound
  unless ← Lean.Meta.isDefEq a.type t.type do throwError "New published type differs: legendreArchimedeanTripleBound"
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.legendreArchimedeanTripleBound"), ("type", Json.str (← Lean.Meta.ppExpr a.type).pretty)])
  let a ← getConstInfo `AbcAdaptation.Tripod.legendreZeroJRootOfUnity
  let t ← getConstInfo `PlatformAudit_legendreZeroJRootOfUnity
  unless ← Lean.Meta.isDefEq a.type t.type do throwError "New published type differs: legendreZeroJRootOfUnity"
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.legendreZeroJRootOfUnity"), ("type", Json.str (← Lean.Meta.ppExpr a.type).pretty)])
  let a ← getConstInfo `solution
  let t ← getConstInfo `AbcAdaptation.Tripod.canonicalLegendreHeightComparison
  unless ← Lean.Meta.isDefEq a.type t.type do throwError "Original parent type differs"
  IO.FS.writeFile ".local/adaptation/legendre-height-20261114/upload-elaborated-types.json" (Json.pretty (Json.arr rows))
  IO.FS.writeFile ".local/adaptation/legendre-height-20261114/parent-types-equal.json" "true"
