/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean (tateStructureOfTorsion)
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_TateFamily

set_option autoImplicit false

open AbcAdaptation.Reference.Iut NumberField WeierstrassCurve
open scoped Classical Valued

universe u

/-- Full odd-prime torsion over an intermediate field gives a Tate structure at a bad place. -/
theorem AbcAdaptation.Reference.Iut.nonempty_tateStructure_of_torsion
    {F : Type u} [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
    {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
    (K : IntermediateField F Fbar) [NumberField ↥K]
    {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}
    (hVBad : ∀ v ∈ VBad, residueChar v ≠ 2)
    (hmult : ∀ v ∈ VBad, ∀ v₀ : FinitePlace F, FinitePlace.LiesOver v₀ v →
      HasMultiplicativeReductionAt E v₀)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2)
    (TK : AddSubgroup (curveK E K).toAffine.Point)
    (hTK : TK ≤ AddSubgroup.torsionBy (curveK E K).toAffine.Point ℓ)
    (hcard : ℓ * ℓ ≤ Nat.card ↥TK)
    {w : FinitePlace ↥K} (hw : IsBadPlace E K VBad w) :
    Nonempty (TateStructure (curveKw E K w)) := by
  sorry
