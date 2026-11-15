import Lean
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalP1Rational
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalP1DegreeOneRational
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalP1RationalBranchSet

set_option autoImplicit false
open scoped Classical
namespace AbcAdaptation.Tripod.Fermat.Proper
open NoncriticalP1

private theorem rational_mem_withInf {T : Finset Tripod.Qbar} {z : NoncriticalP1.Pt} :
    z ∈ withInf T ↔ z = none ∨ ∃ t ∈ T, z = some t := by
  simp only [withInf, Set.mem_insert_iff, Set.mem_image, Finset.mem_coe]
  constructor
  · rintro (h | ⟨t, ht, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨t, ht, rfl⟩
  · rintro (h | ⟨t, ht, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨t, ht, rfl⟩

end AbcAdaptation.Tripod.Fermat.Proper

open AbcAdaptation
open AbcAdaptation.Tripod.Fermat.Proper
open AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1

theorem solution (T : Finset Tripod.Qbar) (hbd : ∀ y ∈ T, ‖ι y‖ ≤ 1)
    (hdeg : ∀ y ∈ T, deg y ≤ 1) :
    ∃ hs, IsNoncriticalBelyi hs (withInf T) (ofRat 9) := by
  classical
  set T₀ : Finset ℚ := T.preimage (fun q : ℚ => (q : Tripod.Qbar))
    Rat.cast_injective.injOn with hT₀
  obtain ⟨hs, hhs⟩ := noncriticalP1RationalBranchSet T₀ 9 (fun q hq => by
    have := hbd _ (Finset.mem_preimage.mp hq)
    rw [norm_ι_ratCast] at this
    exact_mod_cast this) le_rfl
  refine ⟨hs, hhs.mono ?_⟩
  intro z hz
  rcases rational_mem_withInf.mp hz with rfl | ⟨t, ht, rfl⟩
  · exact Set.mem_insert _ _
  · obtain ⟨q, rfl⟩ := noncriticalP1DegreeOneRational (hdeg t ht)
    exact Set.mem_insert_of_mem _
      ⟨q, Finset.mem_coe.mpr (Finset.mem_preimage.mpr ht), rfl⟩

open Lean
run_meta do
  let actual ← getConstInfo `solution
  let target ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalP1Rational
  unless ← Lean.Meta.isDefEq actual.type target.type do throwError "Exact current target type differs"
  let .thmInfo body := actual | throwError "Expected theorem solution"
  let used := body.value.getUsedConstants
  unless !used.contains `AbcAdaptation.Tripod.Fermat.Proper.noncriticalP1Rational do throwError "Circular target reference"
  let axs ← collectAxioms `solution
  for child in #[`AbcAdaptation.Tripod.Fermat.Proper.noncriticalP1DegreeOneRational, `AbcAdaptation.Tripod.Fermat.Proper.noncriticalP1RationalBranchSet] do
    unless used.contains child do throwError "Required child not consumed {child}"
  unless axs.contains `sorryAx do throwError "Expected Open-child reduction dependency"
  for ax in axs do
    unless #[`propext, `Classical.choice, `Quot.sound, `sorryAx].contains ax do throwError "Unexpected reduction axiom {ax}"
  let result := Json.mkObj [("typeEqualToActualTarget", toJson true), ("circularTargetReference", toJson false), ("axioms", toJson (axs.map toString)), ("usedConstants", toJson (used.map toString)), ("type", toJson (← Lean.Meta.ppExpr actual.type).pretty)]
  IO.FS.writeFile ".local/adaptation/fermat-noncritical-rational-split-20261115/parent-solution-audit.json" (result.pretty ++ "\n")

#print axioms solution
