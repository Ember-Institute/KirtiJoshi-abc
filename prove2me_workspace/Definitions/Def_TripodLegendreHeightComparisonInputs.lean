/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Independent adaptation of Iut/Tripod/Height.lean and TwoAdic.lean.
Archived source hashes are recorded in this unit's source-consumer.json.
Historical upstream revision is unverified. No Iut or Genl module is imported.
-/
/-
Independent source decomposition of Iut/Tripod/Height.lean:657,714,743,490.
Uncompiled draft. Every child fixes the existing actual point field and height.
-/
import Definitions.Def_TripodCanonicalHighHeightInputs

set_option autoImplicit false

namespace AbcAdaptation.Tripod

/-- Source Height.lean:714. No compactness or degree bound is needed. -/
def LegendreFiniteUpperBound : Prop :=
  ∀ x : Pt, finHeight (legendreJ (gen x.1)) ≤
    2 * (finHeight (gen x.1) + finHeight (gen x.1)⁻¹ +
      finHeight (gen x.1 - 1)⁻¹)

/-- Source Height.lean:743. All bad places in the fixed support are retained. -/
def LegendreFiniteLowerBound : Prop :=
  ∀ (K : CompactlyBounded) (x : Pt), x ∈ K.set →
    legendreJ (gen x.1) ≠ 0 →
    2 * (finHeight (gen x.1) + finHeight (gen x.1)⁻¹ +
      finHeight (gen x.1 - 1)⁻¹) ≤
    finHeight (legendreJ (gen x.1)) + 6 * K.c * K.V.card * deg x.1

/-- Source Height.lean:657, with the actual degree [Q(x):Q]. -/
def LegendreArchimedeanTripleBound : Prop :=
  ∀ (K : CompactlyBounded) (x : Pt), x ∈ K.set →
    Height.logHeight₁ (gen x.1) ≤ finHeight (gen x.1) + K.c * deg x.1 ∧
    Height.logHeight₁ (gen x.1)⁻¹ ≤ finHeight (gen x.1)⁻¹ + K.c * deg x.1 ∧
    Height.logHeight₁ (gen x.1 - 1)⁻¹ ≤
      finHeight (gen x.1 - 1)⁻¹ + K.c * deg x.1

/-- Source Height.lean:490 specialized to the existing actual tripod generator. -/
def LegendreZeroJRootOfUnity : Prop :=
  ∀ x : Pt, legendreJ (gen x.1) = 0 → gen x.1 ^ 6 = 1

end AbcAdaptation.Tripod
