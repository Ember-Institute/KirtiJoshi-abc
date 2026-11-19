/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original path Oka/Uniformization/OncePunctured.lean
-/
import Solutions.Source_ReferenceIutCanLiftLatticeComplement
import Solutions.Source_ReferenceIutCanLiftLatticeGenerators
import Solutions.Source_ReferenceIutCanLiftLatticeCommutatorTrace
import Solutions.Source_ReferenceIutCanLiftLatticeUniformization

set_option autoImplicit false

/-!
# Uniformization of once-punctured complex elliptic curves

The lattice-complement covering and its two edge pairings produce the uniformization of an
arbitrary complex elliptic curve in its affine Weierstrass coordinates.
-/

open scoped MatrixGroups UpperHalfPlane

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

open AbcAdaptation.Reference.Heights

/-- The existence part of the once-punctured elliptic-curve uniformization in CanLift,
Proposition 2.7 U1. -/
theorem uniformization_oncePunctured (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    ∃ (A B : SL(2, ℝ)) (π : ℂ → ℂ × ℂ),
      Matrix.trace ((A * B * A⁻¹ * B⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = -2 ∧
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 ∧
      IsUniformization W A B π := by
  obtain ⟨τ, C, hC⟩ := exists_variableChange_latticeCurve W
  let U := latticeComplementCover (periodPair τ)
  refine ⟨Generators.A U, Generators.B U, latticeParameterization τ C ∘ U.Ψ,
    Peripheral.trace_commutator U, Peripheral.trace_A_ne_zero U, ?_⟩
  rw [← hC]
  exact U.uniformizes C (Generators.deckGroup_eq_pmGroup U)

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
