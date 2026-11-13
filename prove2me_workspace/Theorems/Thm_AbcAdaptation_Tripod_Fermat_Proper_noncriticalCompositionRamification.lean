/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent namespace adaptation of Belyi/CurveField/NoncriticalElem.lean compK_spec and NoncriticalBasic.lean ramIdx_pos.
Pinned Belyi: 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
Upstream: https://github.com/lana-agents/belyi.
Source SHA-256: 962260751d00333f25cfcd803626193c053d0a982fb6756823de1cc325f4b783.
-/
import Definitions.Def_FermatNoncriticalRamificationPositive
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalElementaryCompositionRamification

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- Positivity and the source list induction for actual rational elementary
composites, preserving the exact existing all-points target statement. -/
theorem noncriticalCompositionRamification {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ) :
    (∀ P : Place M.K, 0 < ramIdx M hDVR ψ P) ∧
    ∀ (hs : List NoncriticalP1.ElemMap) (x : QbarPoint M.K),
      Transcendental ℚ (NoncriticalP1.compK hs ψ) ∧
      noncriticalValue M x (NoncriticalP1.compK hs ψ) =
        NoncriticalP1.evalComp hs (noncriticalValue M x ψ) ∧
      ramIdx M hDVR (NoncriticalP1.compK hs ψ) x.P =
        ramIdx M hDVR ψ x.P *
          (NoncriticalP1.ramIdxComp hs (noncriticalValue M x ψ) : ℤ) := by
  refine ⟨noncriticalRamificationPositive M hDVR ψ hψ, ?_⟩
  intro hs x
  induction hs generalizing ψ with
  | nil =>
    exact ⟨hψ, rfl, by simp [NoncriticalP1.compK, NoncriticalP1.ramIdxComp]⟩
  | cons h hs ih =>
    obtain ⟨h1, h2, h3⟩ :=
      noncriticalElementaryCompositionRamification M hDVR ψ hψ x h
    obtain ⟨i1, i2, i3⟩ := ih (ψ := NoncriticalP1.applyK h ψ) h1
    refine ⟨i1, ?_, ?_⟩
    · change noncriticalValue M x (NoncriticalP1.compK hs (NoncriticalP1.applyK h ψ)) = _
      rw [i2, h2]
      rfl
    · change ramIdx M hDVR (NoncriticalP1.compK hs (NoncriticalP1.applyK h ψ)) x.P = _
      rw [i3, h3, h2]
      simp only [NoncriticalP1.ramIdxComp, Nat.cast_mul, mul_assoc]

end AbcAdaptation.Tripod.Fermat.Proper
