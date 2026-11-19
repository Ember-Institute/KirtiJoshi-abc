/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tower/Main.lean (the step_iii field)
-/
import Solutions.Source_ReferenceIutConcreteInvariants
import Solutions.Source_ReferenceIutTowerStepIII

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField
open scoped BigOperators

universe u v

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {D : InitialThetaData AG TG} {LT : LocalTheory.{u, v} D.Kt}

/-- Step (iii) for the distinguished primes of the given local data. -/
theorem ThetaLocalData.step_iii_of_localFacts (TL : ThetaLocalData D LT)
    (H : TowerLocalFacts D.E D.VBad D.prime) (he2 : RelRamIdxModLeTwo D.E D.VBad)
    [IsGalois ↥(fieldOfModuli D.F D.E) ↥D.tripodalField]
    (hfin : (badPlacesOver D.F D.E D.VBad).Finite)
    (hbad : ∀ p ∈ TL.badChars, ∃ w ∈ badPlacesOver D.F D.E D.VBad, residueChar w = p) :
    ∑ p ∈ TL.dst, Real.log p ≤
      2 * D.dmod * (logDifferentDeg ↥D.tripodalField + D.logConductorDeg) + 5 + Real.log D.ℓ := by
  refine sum_log_distinguished_le H he2 hfin TL.dst fun p hp => ?_
  simp only [ThetaLocalData.dst, Finset.mem_union] at hp
  rcases hp with (hsmall | hbadChar) | hram
  · exact Or.inl hsmall
  · exact Or.inr (Or.inl (hbad p hbadChar))
  · simp only [LocalTheory.ramifiedChars, Finset.mem_image, Set.Finite.mem_toFinset] at hram
    obtain ⟨w, hw, hwp⟩ := hram
    exact Or.inr (Or.inr ⟨w, hwp, hw⟩)

end AbcAdaptation.Reference.Iut
