import Definitions.Def_FermatCurveFieldBasic
import Definitions.Def_FermatCurveFieldChart
import Definitions.Def_FermatCurveFieldPlace
import Definitions.Def_FermatCurveFieldResidue
import Definitions.Def_FermatCurveFieldZerosPoles
import Definitions.Def_FermatRiemannSpaces
import Definitions.Def_FermatRiemannComposition
import Definitions.Def_FermatFunctionDivisors
import Definitions.Def_FermatRiemannLocalDimension
import Definitions.Def_FermatRiemannDimensionComposition

set_option autoImplicit false
open scoped IntermediateField

theorem AbcAdaptation.Tripod.Fermat.Proper.functionZeroPoleDegrees : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M)
  (f : ↥M.K),
  Transcendental ℚ f →
    AbcAdaptation.Tripod.Fermat.Proper.divisorDegree M
          (AbcAdaptation.Tripod.Fermat.Proper.functionZeroDivisor M hDVR f) =
        ↑(Module.finrank ↥ℚ⟮f⟯ ↥M.K) ∧
      AbcAdaptation.Tripod.Fermat.Proper.divisorDegree M
          (AbcAdaptation.Tripod.Fermat.Proper.functionPoleDivisor M hDVR f) =
        ↑(Module.finrank ↥ℚ⟮f⟯ ↥M.K) := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.riemannPolarApproximation : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M)
  (A : AbcAdaptation.Tripod.Fermat.Proper.Divisor M),
  ∃ (z : ↥M.K),
    z ≠ 0 ∧
      ∃ (l : ℕ),
        A + AbcAdaptation.Tripod.Fermat.Proper.functionDivisor M hDVR z ≤
          l • AbcAdaptation.Tripod.Fermat.Proper.functionPoleDivisor M hDVR M.u := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.riemannBasisPowerLowerBound : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M),
  (∀ (A : AbcAdaptation.Tripod.Fermat.Proper.Divisor M),
      FiniteDimensional ℚ ↥(AbcAdaptation.Tripod.Fermat.Proper.riemannRochSpace M hDVR A)) →
    ∀ (l : ℕ),
      (l + 1) * N ≤
        AbcAdaptation.Tripod.Fermat.Proper.riemannEll M hDVR
          (l • AbcAdaptation.Tripod.Fermat.Proper.functionPoleDivisor M hDVR M.u +
            AbcAdaptation.Tripod.Fermat.Proper.basisPoleCorrection M hDVR) := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.riemannRochFiniteDimensional : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M)
  (A : AbcAdaptation.Tripod.Fermat.Proper.Divisor M),
  FiniteDimensional ℚ ↥(AbcAdaptation.Tripod.Fermat.Proper.riemannRochSpace M hDVR A) := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.riemannRochDimensionUpperBound : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M)
  (A : AbcAdaptation.Tripod.Fermat.Proper.Divisor M),
  ↑(AbcAdaptation.Tripod.Fermat.Proper.riemannEll M hDVR A) ≤
    Max.max 0
      (AbcAdaptation.Tripod.Fermat.Proper.divisorDegree M A + ↑(AbcAdaptation.Tripod.Fermat.Proper.riemannEll M hDVR 0)) := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.riemannRochEventuallyLinear : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M),
  ∃ (g0 : ℤ) (N0 : ℤ),
    ∀ (A : AbcAdaptation.Tripod.Fermat.Proper.Divisor M),
      N0 ≤ AbcAdaptation.Tripod.Fermat.Proper.divisorDegree M A →
        ↑(AbcAdaptation.Tripod.Fermat.Proper.riemannEll M hDVR A) =
          AbcAdaptation.Tripod.Fermat.Proper.divisorDegree M A - g0 := by sorry

set_option pp.fullNames true
set_option pp.funBinderTypes true
open Lean
run_meta do
  let mut rows : Array Json := #[]
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.functionZeroPoleDegrees
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.functionZeroPoleDegrees"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.riemannPolarApproximation
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.riemannPolarApproximation"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.riemannBasisPowerLowerBound
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.riemannBasisPowerLowerBound"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.riemannRochFiniteDimensional
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.riemannRochFiniteDimensional"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.riemannRochDimensionUpperBound
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.riemannRochDimensionUpperBound"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.riemannRochEventuallyLinear
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.riemannRochEventuallyLinear"), ("type", Json.str fmt.pretty)])
  IO.FS.writeFile ".local/adaptation/fermat-riemann-20261113/upload-elaborated-types.json" (Json.pretty (Json.arr rows))
