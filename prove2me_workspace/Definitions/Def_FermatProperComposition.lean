/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Definitions.Def_FermatProperCarrier

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- Existence and each concrete geometric fact are independent explicit
children. The composition itself has no geometric assumption beyond them. -/
theorem noncriticalInput_of_children
    (hModel : ∀ N : ℕ, 3 < N → Nonempty (Model N))
    (hDiscrete : ∀ {N : ℕ} (M : Model N), PlacesDiscrete M)
    (hFinite : ∀ {N : ℕ} (M : Model N), ResiduesFinite M)
    (hAffine : ∀ {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M),
      ResiduesFinite M → Nonempty (AffineIdentification M))
    (hBelyi : ∀ {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M),
      ResiduesFinite M → NoncriticalSelection M hDVR)
    (hCusps : ∀ {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M),
      ResiduesFinite M → ∀ φ : M.K,
        IsBelyi M hDVR φ → (cusps M hDVR φ).Finite)
    (N : ℕ) (hN : 3 < N) : NoncriticalInput N := by
  obtain ⟨M⟩ := hModel N hN
  have hDVR := hDiscrete M
  have hRF := hFinite M
  exact ⟨M, hDVR, hRF, hAffine M hDVR hRF,
    hBelyi M hDVR hRF, hCusps M hDVR hRF⟩

end AbcAdaptation.Tripod.Fermat.Proper
