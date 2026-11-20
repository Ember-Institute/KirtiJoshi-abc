/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original paths OrbicurveCores/Classification.lean, lines 29–35, and
OrbicurveCores/S1/Belyi.lean, lines 71–105
-/
import Solutions.Source_ReferenceIutCanLiftLatticeCommutatorTrace
import Solutions.Source_ReferenceIutCanLiftLatticeGenerators
import Solutions.Source_ReferenceIutCanLiftLatticeUniformization
import Solutions.Source_ReferenceIutCanLiftNielsenDescent
import Solutions.Source_ReferenceIutCanLiftTakeuchiBelyiPullback
import Solutions.Source_ReferenceIutCanLiftTakeuchiFourGroups
import Solutions.Source_ReferenceIutCanLiftTakeuchiIntegralTraces
import Solutions.Source_ReferenceIutCanLiftTakeuchiModelRigidity

set_option autoImplicit false

open AbcAdaptation.Reference.Heights (periodPair)
open Matrix.SpecialLinearGroup (toGL)
open scoped MatrixGroups UpperHalfPlane

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi

/-- After changing generators and choosing their signs, the pair is simultaneously conjugate
to one of the four Takeuchi pairs. -/
def IsTakeuchiConj (A B : SL(2, ℝ)) : Prop :=
  ∃ A' B' : SL(2, ℝ), Subgroup.closure {A', B'} = Subgroup.closure {A, B} ∧
    ∃ i : Fin 4, ∃ A'' ∈ ({A', -A'} : Set SL(2, ℝ)), ∃ B'' ∈ ({B', -B'} : Set SL(2, ℝ)),
      ∃ g : GL (Fin 2) ℝ, g * toGL A'' * g⁻¹ = toGL (takeuchiPair i).1 ∧
        g * toGL B'' * g⁻¹ = toGL (takeuchiPair i).2

/-- An elliptic curve with a Belyi certificate for its Weierstrass cubic is uniformized
by a Takeuchi group. -/
theorem exists_takeuchi (hJ : JOrbStatement) {f N D H K R : Polynomial ℂ} {c : ℂ}
    (hc : RatCert f N D H K R c) (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (h1 : W.a₁ = 0) (h3 : W.a₃ = 0)
    (hf : ∀ x, f.eval x = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) :
    ∃ A B : SL(2, ℝ), Uniformizes W (A, B) ∧ IsTakeuchiConj A B := by
  obtain ⟨τ, C, rfl⟩ := exists_variableChange_latticeCurve W
  obtain ⟨hFo, hFl, hFp⟩ := hc.ellipticOrbifoldCover τ C h1 h3 hf
  let U := latticeComplementCover (periodPair τ)
  have hint := int_sq_traces orbLiftStatement hJ τ hFo hFl hFp
  obtain ⟨A', B', hcl, hc', hT⟩ :=
    takeuchi_one_infty_of_int (Peripheral.trace_commutator U) (Peripheral.trace_A_ne_zero U) hint
  obtain ⟨i, A'', hA'', B'', hB'', g, hgA, hgB⟩ := exists_conj_of_takeuchiSq hc' hT
  exact ⟨Generators.A U, Generators.B U, ⟨_, U.uniformizes C (Generators.deckGroup_eq_pmGroup U)⟩,
    A', B', hcl, i, A'', hA'', B'', hB'', g, hgA, hgB⟩

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi
