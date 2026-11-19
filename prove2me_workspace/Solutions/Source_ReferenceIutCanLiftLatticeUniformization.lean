/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original path Oka/Uniformization/OncePunctured.lean
-/
import Solutions.Source_ReferenceIutCanLiftLatticeDeckGroup
import Solutions.Source_ReferenceIutCanLiftLatticeParameterization

set_option autoImplicit false

open scoped MatrixGroups UpperHalfPlane

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

open AbcAdaptation.Reference.Heights
open WeierstrassCurve

namespace LatticeComplementCover

/-- A covering of the lattice complement with specified deck generators gives a uniformization
of the affine lattice curve in the chosen coordinates. -/
theorem uniformizes {τ : ℍ} (U : LatticeComplementCover (periodPair τ))
    (C : VariableChange ℂ) {A B : SL(2, ℝ)}
    (hdeck : U.deckGroup = IsUniformization.pmGroup A B) :
    IsUniformization (C • latticeCurve τ) A B (latticeParameterization τ C ∘ U.Ψ) := by
  apply isUniformization_latticeParameterization τ C U.ψ_notMem U.holo U.surj
  intro z w
  rw [← hdeck]
  exact U.sub_mem_lattice_iff

end LatticeComplementCover

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
