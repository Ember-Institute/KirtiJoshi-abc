/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent namespace adaptation of Belyi/CurveField/NoncriticalBasic.lean ramIdx_pos and necessary residue-polynomial helpers.
Pinned Belyi: 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
Upstream: https://github.com/lana-agents/belyi.
Source SHA-256: NoncriticalBasic=0bbc09343228185b5c499b9f4563dbcb69fd6338e7b05c107ad784149bfc01a3; RamIdx=14ad110ef89ced20c49856589f6c586bb93a7fa6ec7bfb9eb606ba7b023cd4f6; CurveDeriv.Local=cb930e45cba81a1377ab8281264d938868ae7834d32c480a9af9d29012eb1aae.
-/
import Definitions.Def_FermatNoncriticalFunctions
import Mathlib.Algebra.Algebra.Hom.Rat

set_option autoImplicit false

open Polynomial

namespace AbcAdaptation.Tripod.Fermat.Proper

namespace Place

variable {K : Type*} [Field K] [CharZero K] (P : Place K)

/-- Source CurveDeriv/Local.lean `aeval_mem`, specialized to the actual
valuation ring of P. Only this polynomial-membership proof is reused;
no derivative carrier or local derivative theorem is imported. -/
theorem noncritical_aeval_mem {x : K} (hx : x ∈ P.1) (p : ℚ[X]) : aeval x p ∈ P.1 := by
  rw [aeval_eq_sum_range]
  refine sum_mem fun i _ => ?_
  rw [Algebra.smul_def]
  exact mul_mem (P.algebraMap_mem _) (pow_mem hx _)

/-- Source CurveField/RamIdx.lean `residue_aeval`, using the actual residue map. -/
theorem noncritical_residue_aeval {x : K} (hx : x ∈ P.1) (p : ℚ[X]) :
    P.residue ⟨aeval x p, P.noncritical_aeval_mem hx p⟩ =
      aeval (P.residue ⟨x, hx⟩) p := by
  have h1 : (⟨aeval x p, P.noncritical_aeval_mem hx p⟩ : P.1) =
      eval₂ P.ratHom ⟨x, hx⟩ p := by
    apply Subtype.ext
    change aeval x p = P.1.subtype (eval₂ P.ratHom ⟨x, hx⟩ p)
    rw [hom_eval₂, aeval_def]
    congr 1
  rw [h1, hom_eval₂, aeval_def]
  congr 1
  exact RingHom.ext_rat _ _

variable [IsCurveField K]

/-- Source CurveField/RamIdx.lean `isIntegral_residue`; finiteness of the
full actual residue field is supplied by the existing curve-field instance. -/
theorem noncritical_isIntegral_residue (a : P.1) : IsIntegral ℚ (P.residue a) :=
  Algebra.IsIntegral.isIntegral _

/-- Source NoncriticalBasic.lean `ord_pos_of_residue_eq_zero`. -/
theorem noncritical_ord_pos_of_residue_eq_zero {y : K} (hy : y ∈ P.1) (hy0 : y ≠ 0)
    (h : P.residue ⟨y, hy⟩ = 0) : 0 < P.ord y :=
  (P.ord_pos_iff_mem_maximalIdeal (a := ⟨y, hy⟩) hy0).mpr
    ((P.residue_eq_zero_iff).mp h)

end Place

/-- Source NoncriticalBasic.lean `ramIdx_pos`, at the existing model's
actual residue-minpoly/pole index. This is a completed source proof. -/
theorem noncriticalRamificationPositive {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ)
    (P : Place M.K) : 0 < ramIdx M hDVR ψ P := by
  letI : IsCurveField M.K := M.isCurveField
  unfold ramIdx
  split_ifs with h
  · rw [ord_eq_placeOrd]
    have hr := P.noncritical_isIntegral_residue ⟨ψ, h⟩
    have hm0 : aeval ψ (minpoly ℚ (P.residue ⟨ψ, h⟩)) ≠ 0 :=
      fun h0 => hψ ⟨_, minpoly.ne_zero hr, h0⟩
    refine P.noncritical_ord_pos_of_residue_eq_zero (P.noncritical_aeval_mem h _) hm0 ?_
    rw [P.noncritical_residue_aeval h]
    exact minpoly.aeval ℚ _
  · rw [ord_eq_placeOrd]
    have := (P.ord_neg_iff).mpr h
    omega

end AbcAdaptation.Tripod.Fermat.Proper
