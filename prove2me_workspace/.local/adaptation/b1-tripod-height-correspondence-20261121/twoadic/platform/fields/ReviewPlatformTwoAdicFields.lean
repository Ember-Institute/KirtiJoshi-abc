/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original revision: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_Theory
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_TwoAdicBound

set_option autoImplicit false

open AbcAdaptation.Tripod AbcAdaptation.Reference.Iut

theorem solution (P : CurveProviders) (K : CompactlyBounded) (d : ℕ) :
    0 ≤ max (4 * K.c) 0 ∧
      ∀ (x : tripodTheory.Pt tripodTheory.tripod),
        x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d →
        ((P.curve x).localHeightData (P.arith x) (P.tate x)).heightEq 2 ≤ max (4 * K.c) 0 :=
  ⟨le_max_right _ _, fun x hx => twoAdicBound P K x hx.1⟩

theorem AbcAdaptation.Tripod.curveInputs_twoAdic_fields (P : CurveProviders) (K : CompactlyBounded) (d : ℕ) :
    0 ≤ max (4 * K.c) 0 ∧
      ∀ (x : tripodTheory.Pt tripodTheory.tripod),
        x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d →
        ((P.curve x).localHeightData (P.arith x) (P.tate x)).heightEq 2 ≤ max (4 * K.c) 0 := solution P K d

#print axioms solution
#print axioms AbcAdaptation.Tripod.curveInputs_twoAdic_fields
