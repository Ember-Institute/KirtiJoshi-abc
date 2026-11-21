/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original revision: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviderHeight

namespace AbcAdaptation.Reference.Iut.LocalHeightData

open Finset Real

variable (L : LocalHeightData)

/-- The part of `log(q_∀)` supported at the places of residue characteristic `q`. -/
noncomputable def heightEq (q : ℕ) : ℝ :=
  (∑ v ∈ L.bad.filter (fun v => L.p v = q), (L.hv v : ℝ) * L.f v * Real.log (L.p v)) / L.deg

end AbcAdaptation.Reference.Iut.LocalHeightData

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum WithZero WeierstrassCurve
open scoped WithZero Real Classical

variable (P : CurveProviders) (K : CompactlyBounded)

def TwoAdicBoundHyp (B : ℝ) : Prop := ∀ x ∈ K.set, (P.localData x).heightEq 2 ≤ B

end AbcAdaptation.Tripod
