import Lean
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalP1DegreeOneRational
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalP1RationalBranchSet
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalP1Rational

set_option autoImplicit false
open scoped Classical
namespace AbcAdaptation.Tripod.Fermat.Proper
open NoncriticalP1
open Polynomial IntermediateField

theorem SourceExpected_noncriticalP1DegreeOneRational {x : Qbar} (hx : deg x ≤ 1) : ∃ q : ℚ, x = q := by sorry

theorem SourceExpected_noncriticalP1RationalBranchSet (T : Finset ℚ) (τ : ℚ) (hT : ∀ t ∈ T, |t| ≤ 1)
    (hτ : 9 ≤ τ) :
    ∃ hs : List ElemMap, IsNoncriticalBelyi hs (insert none (ofRat '' (T : Set ℚ))) (ofRat τ) := by sorry

theorem SourceExpected_noncriticalP1Rational (T : Finset Qbar) (hbd : ∀ y ∈ T, ‖ι y‖ ≤ 1)
    (hdeg : ∀ y ∈ T, deg y ≤ 1) :
    ∃ hs, IsNoncriticalBelyi hs (withInf T) (ofRat 9) := by sorry

end AbcAdaptation.Tripod.Fermat.Proper

set_option pp.fullNames true
set_option pp.funBinderTypes true
open Lean
run_meta do
  let mut rows : Array Json := #[]
  let actual ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalP1DegreeOneRational
  let expected ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.SourceExpected_noncriticalP1DegreeOneRational
  unless ← Lean.Meta.isDefEq actual.type expected.type do throwError "Source AST signature type differs: noncriticalP1DegreeOneRational"
  let text ← Lean.Meta.ppExpr actual.type
  rows := rows.push (Json.mkObj [("name", toJson "AbcAdaptation.Tripod.Fermat.Proper.noncriticalP1DegreeOneRational"), ("type", toJson text.pretty), ("actualTypeEqualToCompleteTransportedSourceSignature", toJson true)])
  let actual ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalP1RationalBranchSet
  let expected ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.SourceExpected_noncriticalP1RationalBranchSet
  unless ← Lean.Meta.isDefEq actual.type expected.type do throwError "Source AST signature type differs: noncriticalP1RationalBranchSet"
  let text ← Lean.Meta.ppExpr actual.type
  rows := rows.push (Json.mkObj [("name", toJson "AbcAdaptation.Tripod.Fermat.Proper.noncriticalP1RationalBranchSet"), ("type", toJson text.pretty), ("actualTypeEqualToCompleteTransportedSourceSignature", toJson true)])
  let actual ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalP1Rational
  let expected ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.SourceExpected_noncriticalP1Rational
  unless ← Lean.Meta.isDefEq actual.type expected.type do throwError "Source AST signature type differs: noncriticalP1Rational"
  let text ← Lean.Meta.ppExpr actual.type
  rows := rows.push (Json.mkObj [("name", toJson "AbcAdaptation.Tripod.Fermat.Proper.noncriticalP1Rational"), ("type", toJson text.pretty), ("actualTypeEqualToCompleteTransportedSourceSignature", toJson true)])
  IO.FS.writeFile ".local/adaptation/fermat-noncritical-rational-split-20261115/compiler-types.json" ((Json.arr rows).pretty ++ "\n")
