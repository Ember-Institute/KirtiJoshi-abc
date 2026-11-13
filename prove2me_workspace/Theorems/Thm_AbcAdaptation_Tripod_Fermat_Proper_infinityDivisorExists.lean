/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent finite-support adaptation of Belyi/CurveField/{ZerosPoles,Divisor}.lean
at 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
The hyperplane coefficient follows the tuple-divisor convention in
Heights/Curve/TupleHeight.lean at 721496ca4c158e511d25d8ccf6bfe8503eda73c1.
-/
import Definitions.Def_FermatInfinityDivisorFiniteSupport

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- The exact coordinate hyperplane coefficient has finite support. -/
theorem infinityDivisorExists {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    (hRF : ResiduesFinite M) : Nonempty (InfinityDivisorData M hDVR) :=
  ⟨coordinateInfinityData M hDVR⟩

end AbcAdaptation.Tripod.Fermat.Proper
