import Lean
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalP1Zero

set_option autoImplicit false
open scoped IntermediateField

theorem PlatformAudit_noncriticalP1Zero : ∀ (S : Finset AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.Pt),
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

open Lean
run_meta do
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalP1Zero
  let p ← getConstInfo `PlatformAudit_noncriticalP1Zero
  unless ← Lean.Meta.isDefEq a.type p.type do throwError "Original platform target type differs: noncriticalP1Zero"
  IO.FS.writeFile ".local/adaptation/fermat-noncritical-p1-20261114/existing-types-equal.json" "true"
