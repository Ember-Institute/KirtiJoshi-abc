import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalPolynomialOrderAtRegularPoint
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalPolynomialOrderAtPole
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalInverseRamification
import Definitions.Def_FermatNoncriticalElementarySource

set_option autoImplicit false
open Polynomial
open scoped IntermediateField
open AbcAdaptation
open AbcAdaptation.Tripod.Fermat.Proper

/-- OPEN: exact actual-function-field mathematical boundary from Belyi/CurveField/NoncriticalBasic.lean ord_aeval_eq. -/
theorem ExportTarget_noncriticalPolynomialOrderAtRegularPoint {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ)
    (x : QbarPoint M.K) (h : ψ ∈ x.P.1) {g : ℚ[X]} (hg : g ≠ 0) :
    letI : IsCurveField M.K := M.isCurveField
    x.P.ord (aeval ψ g) = ramIdx M hDVR ψ x.P *
      ((g.map (algebraMap ℚ Tripod.Qbar)).rootMultiplicity (x.eval ψ h) : ℤ) := by
  letI : IsCurveField M.K := M.isCurveField
  sorry

/-- OPEN: exact actual-function-field mathematical boundary from Belyi/CurveField/NoncriticalElem.lean ord_aeval_of_notMem. -/
theorem ExportTarget_noncriticalPolynomialOrderAtPole {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ)
    (P : Place M.K) (h : ψ ∉ P.1) {p : ℚ[X]} (hp : p ≠ 0) :
    letI : IsCurveField M.K := M.isCurveField
    P.ord (aeval ψ p) = p.natDegree * P.ord ψ := by
  letI : IsCurveField M.K := M.isCurveField
  sorry

/-- OPEN: exact actual-function-field mathematical boundary from Belyi/CurveField/NoncriticalElem.lean inv_spec second conjunct. -/
theorem ExportTarget_noncriticalInverseRamification {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ)
    (x : QbarPoint M.K) :
    ramIdx M hDVR ψ⁻¹ x.P = ramIdx M hDVR ψ x.P := by
  letI : IsCurveField M.K := M.isCurveField
  sorry

set_option pp.fullNames true
set_option pp.funBinderTypes true
open Lean
run_meta do
  let mut rows : Array Json := #[]
  let info ← getConstInfo `ExportTarget_noncriticalPolynomialOrderAtRegularPoint
  let original ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalPolynomialOrderAtRegularPoint
  unless ← Lean.Meta.isDefEq info.type original.type do throwError "Exported source target type differs: noncriticalPolynomialOrderAtRegularPoint"
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.noncriticalPolynomialOrderAtRegularPoint"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `ExportTarget_noncriticalPolynomialOrderAtPole
  let original ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalPolynomialOrderAtPole
  unless ← Lean.Meta.isDefEq info.type original.type do throwError "Exported source target type differs: noncriticalPolynomialOrderAtPole"
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.noncriticalPolynomialOrderAtPole"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `ExportTarget_noncriticalInverseRamification
  let original ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalInverseRamification
  unless ← Lean.Meta.isDefEq info.type original.type do throwError "Exported source target type differs: noncriticalInverseRamification"
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.noncriticalInverseRamification"), ("type", Json.str fmt.pretty)])
  IO.FS.writeFile ".local/adaptation/fermat-noncritical-elementary-20261114/upload-elaborated-types.json" (Json.pretty (Json.arr rows))
  IO.FS.writeFile ".local/adaptation/fermat-noncritical-elementary-20261114/export-types-equal.json" "true"
