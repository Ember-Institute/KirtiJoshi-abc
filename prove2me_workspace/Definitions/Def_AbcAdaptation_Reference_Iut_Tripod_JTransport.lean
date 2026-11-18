/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Authors: The iut contributors
-/
/-
Uncompiled draft: source declaration bodies selected byte-for-byte; wrappers and imports adapted.
Original repository: https://github.com/lana-agents/iut
Original revision recorded by existing adaptation: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
This draft does not itself establish accepted AST-command provenance.
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FieldTransport
import Definitions.Def_TripodCanonicalHighHeightInputs

namespace AbcAdaptation.Tripod
open WeierstrassCurve NumberField

lemma map_legendreJ {R S F : Type*} [Field R] [Field S] [FunLike F R S] [RingHomClass F R S]
    (f : F) (l : R) : f (legendreJ l) = legendreJ (f l) := by
  simp only [legendreJ, map_div₀, map_mul, map_pow, map_sub, map_add, map_one, map_ofNat]

open WeierstrassCurve AbcAdaptation.Tripod in
/-- `j(E_λ) = legendreJ λ`. -/
lemma legendre_j_eq_legendreJ {R : Type*} [Field R] [NeZero (2 : R)] {l : R}
    [(legendre l).IsElliptic] : (legendre l).j = legendreJ l :=
  legendre_j

variable (P : CurveProviders) (x : Pt)

/-- `j(E_λ)` as an element of `F_tpd`. -/
noncomputable abbrev jT : tpd P x := legendreJ (genT P x)

/-- `j(E_λ) = legendreJ λ` in `F_λ`. -/
theorem curve_j_eq_legendreJ : (P.curve x).E.j = legendreJ (genC' P x) := by
  change (legendre (genC' P x)).j = _
  exact legendre_j_eq_legendreJ

/-- `j(E_λ)` comes from `F_tpd`. -/
theorem curve_j_eq_algebraMap :
    (P.curve x).E.j = algebraMap (tpd P x) (P.curve x).F (jT P x) := by
  rw [curve_j_eq_legendreJ, jT, map_legendreJ, algebraMap_genT]

/-- `F_tpd ≅ ℚ(λ)` maps `j` to `legendreJ λ`. -/
theorem tpdEquiv_jT : tpdEquiv P x (jT P x) = legendreJ (gen x.1) := by
  rw [jT, map_legendreJ, tpdEquiv_genT]

end AbcAdaptation.Tripod
