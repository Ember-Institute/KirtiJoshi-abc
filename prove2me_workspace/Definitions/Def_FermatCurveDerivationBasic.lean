/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent namespace adaptation of Belyi/CurveDeriv/Basic.lean derivAlong.
Pinned Belyi: 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
Upstream: https://github.com/lana-agents/belyi.
Source SHA-256: cf1b11adab96fbd7d7bb5114e7215dcbf8b8cda1a8eda573e9759ac5316f40b2.
-/
import Definitions.Def_FermatCurveDerivationEtale
import Definitions.Def_FermatCurveDerivationPolynomial

set_option autoImplicit false

open scoped IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

variable {K : Type*} [Field K] [CharZero K] (t : K)

open Classical in
/-- The derivation `d/dt` of `K`: the unique `ℚ`-derivation of `K` with `t ↦ 1`, when `t` is
transcendental over `ℚ` and `K` is algebraic over `ℚ⟮t⟯` (and `0` otherwise). -/
noncomputable def derivAlong : Derivation ℚ K K :=
  if h : Transcendental ℚ t ∧ Algebra.IsAlgebraic ℚ⟮t⟯ K then
    have := h.2
    have := formallyEtale_adjoin t
    extendOfFormallyEtale (polyDeriv t h.1)
  else 0

end AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv
