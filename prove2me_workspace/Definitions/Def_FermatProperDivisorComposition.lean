/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors
-/
import Definitions.Def_FermatProperDivisorHeight

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- The geometric and Riemann existence children produce concrete arithmetic
inputs. They do not assert, or assume as a field, the parent estimate. -/
theorem arithmeticDivisorChoices_of_children
    (hPolar : ∀ {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M),
      ResiduesFinite M → ∀ D : Divisor M, Nonempty (PolarPresentation M hDVR D))
    (hCanonical : ∀ {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M),
      ResiduesFinite M → Nonempty (CanonicalDivisorData M hDVR))
    (hInfinity : ∀ {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M),
      ResiduesFinite M → Nonempty (InfinityDivisorData M hDVR))
    (hAdjunction : ∀ {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M),
      3 < N → ResiduesFinite M → ∀ (K : CanonicalDivisorData M hDVR)
        (H : InfinityDivisorData M hDVR), Nonempty (PlaneAdjunctionData M hDVR K H))
    (hGenerators : ∀ {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M),
      ResiduesFinite M → ∀ (φ : M.K), IsBelyi M hDVR φ →
      ∀ hfin : (cusps M hDVR φ).Finite, Nonempty (CuspGenerators M hDVR φ hfin))
    {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M) (hN : 3 < N)
    (hRF : ResiduesFinite M) (φ : M.K) (hφ : IsBelyi M hDVR φ)
    (hfin : (cusps M hDVR φ).Finite) :
    Nonempty (ArithmeticDivisorChoices M hDVR φ hfin) := by
  obtain ⟨K⟩ := hCanonical M hDVR hRF
  obtain ⟨H⟩ := hInfinity M hDVR hRF
  obtain ⟨J⟩ := hAdjunction M hDVR hN hRF K H
  obtain ⟨RK⟩ := hPolar M hDVR hRF K.D
  obtain ⟨RE⟩ := hPolar M hDVR hRF (cuspDivisor M hDVR φ hfin)
  obtain ⟨G⟩ := hGenerators M hDVR hRF φ hφ hfin
  exact ⟨⟨K, H, J, RK, RE, G⟩⟩

end AbcAdaptation.Tripod.Fermat.Proper
