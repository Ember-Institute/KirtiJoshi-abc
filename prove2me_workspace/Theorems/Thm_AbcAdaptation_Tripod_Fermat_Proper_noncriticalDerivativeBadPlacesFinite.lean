/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent namespace adaptation of Belyi/CurveField/NoncriticalFinite.lean finite_setOf_derivAlong_notMem.
Pinned Belyi: 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
Upstream: https://github.com/lana-agents/belyi.
Source SHA-256: 97605e681191f8a923c7de80df284e327550f708a884b5deb135e469b6a2bbf8.
-/
import Definitions.Def_FermatNoncriticalFunctions
import Definitions.Def_FermatCurveDerivationLocalization

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- The actual derivative with respect to ψ preserves all but finitely many
actual local rings containing ψ, over the full valuative place carrier. -/
theorem noncriticalDerivativeBadPlacesFinite {N : ℕ} (M : Model N)
    (ψ : M.K) (hψ : Transcendental ℚ ψ) :
    {P : Place M.K | ψ ∈ P.1 ∧
      ∃ s ∈ P.1, CurveDeriv.derivAlong ψ s ∉ P.1}.Finite := by
  letI : IsCurveField M.K := M.isCurveField
  haveI : Fact (Transcendental ℚ ψ) := ⟨hψ⟩
  letI : Algebra (Algebra.adjoin ℚ {ψ}) (chartRing ψ) := (chartRing ψ).algebra'
  letI : Module (Algebra.adjoin ℚ {ψ}) (chartRing ψ) := Algebra.toModule
  obtain ⟨G, hG⟩ := Module.Finite.fg_top
    (R := Algebra.adjoin ℚ {ψ}) (M := chartRing ψ)
  refine (G.finite_toSet.biUnion fun g _ ↦
    Place.finite_setOf_notMem (CurveDeriv.derivAlong ψ (g : M.K))).subset ?_
  rintro P ⟨hψP, s, hs, hDs⟩
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  by_contra hgood
  push Not at hgood
  apply hDs
  have hA : ∀ r : chartRing ψ, CurveDeriv.derivAlong ψ (r : M.K) ∈ P.1 :=
    CurveDeriv.derivAlong_mem_chartRing_of_generators hψ P hψP G hG hgood
  exact CurveDeriv.derivAlong_mem_place_of_chartRing P hψP hA hs

end AbcAdaptation.Tripod.Fermat.Proper
