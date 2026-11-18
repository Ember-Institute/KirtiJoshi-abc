/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/CurveFacts.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviderHeight
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_Theory
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_PrimeSelection_HeightParts

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField

variable (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)

/-- The cyclic subgroup estimate away from 2 used by Corollary 2.2. -/
def CyclicBoundOddHyp (TK : ℝ) : Prop :=
  ∀ x ∈ K.set ∩ ptLE d, ∀ ℓ : ℕ, ℓ.Prime → 7 ≤ ℓ →
    (∀ w ∈ (P.localData x).bad, ¬ ℓ ∣ (P.localData x).hv w) →
    (P.curve x).HasCyclicSubgroup ℓ →
    ((ℓ : ℝ) - 2) / 24 * (P.h x - (P.localData x).heightEq 2) ≤ 2 * Real.log ℓ + TK

/-- The special linear subgroup lies in the image under (P2), (P4) and (P5). -/
def SL2ImageHyp : Prop :=
  ∀ (x : Pt) (ℓ : ℕ) (hℓ : ℓ.Prime), 5 ≤ ℓ →
    (∀ w ∈ (P.localData x).bad, ¬ ℓ ∣ (P.localData x).hv w) →
    ¬ (P.curve x).HasCyclicSubgroup ℓ →
    (∃ w ∈ (P.localData x).bad, (P.localData x).p w ≠ 2 ∧ (P.localData x).p w ≠ ℓ) →
    ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), A.toGL ∈ (P.modRep x ℓ hℓ).rep.range

/-- The normalized conductor degree away from 2 and ℓ is bounded by the point conductor. -/
def LogCondGeHyp : Prop :=
  ∀ (x : Pt) (ℓ : ℕ), ℓ.Prime → 7 ≤ ℓ →
    logConductorDegOf (P.curve x).F (P.curve x).E ((P.curve x).VBadOf ℓ) ≤ logCond x

/-- The reverse conductor comparison includes the contribution at 2 and ℓ. -/
def LogCondLeHyp : Prop :=
  ∀ (x : Pt) (ℓ : ℕ), ℓ.Prime → 7 ≤ ℓ →
    logCond x ≤
      logConductorDegOf (P.curve x).F (P.curve x).E ((P.curve x).VBadOf ℓ) + Real.log (2 * ℓ)

/-- Finiteness of the exceptional set for the core condition on the degree locus. -/
def CoreFinitenessHyp (AG : AnabelianGeometry.{0}) : Prop :=
  {x | ∃ hx : x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d,
    ¬ OrbicurveDataSection.HasCoreUniversally AG (P.curve x).F (P.curve x).E}.Finite

/-- The cyclic estimate consumed by the curve input constructor. -/
structure CurveFactsProp (TK : ℝ) : Prop where
  cyclic : CyclicBoundOddHyp P K d TK

end AbcAdaptation.Tripod
