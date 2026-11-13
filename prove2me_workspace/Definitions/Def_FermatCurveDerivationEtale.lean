/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent namespace adaptation of Belyi/CurveDeriv/Basic.lean Derivation.extendOfFormallyEtale.
Pinned Belyi: 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
Upstream: https://github.com/lana-agents/belyi.
Source SHA-256: cf1b11adab96fbd7d7bb5114e7215dcbf8b8cda1a8eda573e9759ac5316f40b2.
-/
import Mathlib.RingTheory.Etale.Kaehler

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

section Extension

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T]

open KaehlerDifferential TensorProduct

/-- Extension of a derivation `d : S → T` to a derivation `T → T` when `T` is formally étale
over `S`: the composite `Ω[T⁄R] ≅ T ⊗[S] Ω[S⁄R] → T`. -/
noncomputable def extendOfFormallyEtale [Algebra.FormallyEtale S T]
    (d : Derivation R S T) : Derivation R T T :=
  ((LinearMap.liftBaseChange T d.liftKaehlerDifferential) ∘ₗ
    (tensorKaehlerEquivOfFormallyEtale R S T).symm.toLinearMap).compDer (KaehlerDifferential.D R T)

end Extension

end AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv
