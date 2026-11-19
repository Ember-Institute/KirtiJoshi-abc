/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Concrete/LocalConstruct/LogShell.lean
-/
import Solutions.Source_ReferenceIutConcreteLocalFiniteIndeterminacy
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorUnramifiedLogShell
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorLogShellIndeterminacy

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.LocalConstruct

open MeasureTheory NumberField

universe u

noncomputable section

variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K)

open Classical in
/-- Transport the normalization-module span of the completion tensor log-shell.
In a zero-ring packet the integral structure is the whole packet. -/
def finiteLogShell : Set (Tensor K (.finite p) c) :=
  if hc : ∀ j, IsOver K p (c j) then
    genuineTensorEquiv p c hc '' ↑((genuinePacket p c hc).saturatedLogShell)
  else integral p c

private theorem finiteLogShell_eq_image_of_isOver (hc : ∀ j, IsOver K p (c j)) :
    finiteLogShell p c =
      genuineTensorEquiv p c hc '' ↑((genuinePacket p c hc).saturatedLogShell) := by
  rw [finiteLogShell, dif_pos hc]

private theorem isCompact_finiteLogShell : IsCompact (finiteLogShell p c) := by
  classical
  by_cases hc : ∀ j, IsOver K p (c j)
  · rw [finiteLogShell_eq_image_of_isOver p c hc]
    let e := genuineTensorContinuousLinearEquiv p c hc
    exact (genuinePacket p c hc).saturatedLogShell_isCompact.image e.continuous
  · rw [finiteLogShell, dif_neg hc]
    exact isCompact_integral p c

theorem isCompact_closure_finiteLogShell : IsCompact (closure (finiteLogShell p c)) := by
  have h := isCompact_finiteLogShell p c
  simpa only [h.isClosed.closure_eq] using h

theorem integral_subset_finiteLogShell : integral p c ⊆ finiteLogShell p c := by
  classical
  by_cases hc : ∀ j, IsOver K p (c j)
  · rw [finiteLogShell_eq_image_of_isOver p c hc, ← genuineTensorEquiv_image_normalization p c hc]
    exact Set.image_mono (genuinePacket p c hc).normalization_subset_saturatedLogShell
  · simpa only [finiteLogShell, dif_neg hc] using (Set.Subset.rfl : integral p c ⊆ integral p c)

theorem finiteLogShell_eq_integral_of_unramified (hodd : Odd (p : ℕ))
    (he : ∀ j w, c j = Place.finite w → ramIdx K w = 1) :
    finiteLogShell p c = integral p c := by
  classical
  by_cases hc : ∀ j, IsOver K p (c j)
  · let P := genuinePacket p c hc
    have hram (j : ι) : JoshiTeich.Prologue.Arithmetic.ramIdx (P.place j) = 1 := by
      obtain ⟨w, hw, -⟩ := hc j
      change ramIdx K (finPart K (c j)) = 1
      rw [← eq_finPart hw]
      exact he j w hw
    rw [finiteLogShell_eq_image_of_isOver p c hc,
      P.saturatedLogShell_eq_normalization_of_unramified hodd hram,
      genuineTensorEquiv_image_normalization p c hc]
  · rw [finiteLogShell, dif_neg hc]

theorem finiteIndAut_logShell :
    ∀ φ ∈ finiteIndAut p c, φ '' finiteLogShell p c ⊆ finiteLogShell p c := by
  intro φ hφ
  classical
  by_cases hc : ∀ j, IsOver K p (c j)
  · rw [finiteIndAut_eq_image_of_isOver p c hc] at hφ
    obtain ⟨ψ, hψ, rfl⟩ := hφ
    obtain ⟨σ, rfl⟩ := hψ
    let P := genuinePacket p c hc
    have h : genuineTensorConjugate p c hc (P.factorTensorAut σ) '' finiteLogShell p c =
        finiteLogShell p c := by
      rw [finiteLogShell_eq_image_of_isOver p c hc, genuineTensorConjugate_image,
        P.factorTensorAut_image_saturatedLogShell σ]
    exact h.subset
  · rw [finiteLogShell, dif_neg hc]
    exact prop14_iv p c φ hφ

theorem thetaShell_admissible_finite :
    (⋃ φ ∈ finiteIndAut p c, φ '' finiteLogShell p c) ∈ finiteAdmissible p c :=
  iUnion_finiteIndAut_admissible p c (isCompact_finiteLogShell p c)
    ((finiteHaar_integral_pos p c).trans_le (measure_mono (integral_subset_finiteLogShell p c)))

end

end AbcAdaptation.Reference.Iut.LocalConstruct
