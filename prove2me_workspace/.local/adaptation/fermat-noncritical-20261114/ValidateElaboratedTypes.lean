import Definitions.Def_FermatNoncriticalFunctions
import Definitions.Def_FermatNoncriticalSimpleZeros
import Definitions.Def_FermatNoncriticalComposition

set_option autoImplicit false
open scoped IntermediateField

theorem AbcAdaptation.Tripod.Fermat.Proper.noncriticalRamificationFinite : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M)
  (ψ : ↥M.K),
  Transcendental ℚ ψ →
    {P : AbcAdaptation.Tripod.Fermat.Proper.Place ↥M.K |
        1 < AbcAdaptation.Tripod.Fermat.Proper.ramIdx M hDVR ψ P}.Finite := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.noncriticalCompositionRamification : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M)
  (ψ : ↥M.K),
  Transcendental ℚ ψ →
    (∀ (P : AbcAdaptation.Tripod.Fermat.Proper.Place ↥M.K), 0 < AbcAdaptation.Tripod.Fermat.Proper.ramIdx M hDVR ψ P) ∧
      ∀ (hs : List AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.ElemMap)
        (x : AbcAdaptation.Tripod.Fermat.Proper.QbarPoint ↥M.K),
        Transcendental ℚ (AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.compK hs ψ) ∧
          AbcAdaptation.Tripod.Fermat.Proper.noncriticalValue M x
                (AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.compK hs ψ) =
              AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.evalComp hs
                (AbcAdaptation.Tripod.Fermat.Proper.noncriticalValue M x ψ) ∧
            AbcAdaptation.Tripod.Fermat.Proper.ramIdx M hDVR
                (AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.compK hs ψ) x.P =
              AbcAdaptation.Tripod.Fermat.Proper.ramIdx M hDVR ψ x.P *
                ↑(AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.ramIdxComp hs
                    (AbcAdaptation.Tripod.Fermat.Proper.noncriticalValue M x ψ)) := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.noncriticalP1Zero : ∀ (S : Finset AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.Pt),
  (∀ (σ : Gal(AbcAdaptation.Tripod.Qbar/ℚ)), ∀ z ∈ S, Option.map (⇑σ) z ∈ S) →
    Option.some 0 ∉ S →
      ∃ (hs : List AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.ElemMap),
        (∀ z ∈ S,
            AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.evalComp hs z ∈
              AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.zeroOneInf) ∧
          AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.evalComp hs (Option.some 0) ∉
              AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.zeroOneInf ∧
            ∀ (z : AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.Pt),
              1 < AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.ramIdxComp hs z →
                AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.evalComp hs z ∈
                  AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.zeroOneInf := by sorry

set_option pp.fullNames true
set_option pp.funBinderTypes true
open Lean
run_meta do
  let mut rows : Array Json := #[]
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalRamificationFinite
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.noncriticalRamificationFinite"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalCompositionRamification
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.noncriticalCompositionRamification"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalP1Zero
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.noncriticalP1Zero"), ("type", Json.str fmt.pretty)])
  IO.FS.writeFile ".local/adaptation/fermat-noncritical-20261114/upload-elaborated-types.json" (Json.pretty (Json.arr rows))
