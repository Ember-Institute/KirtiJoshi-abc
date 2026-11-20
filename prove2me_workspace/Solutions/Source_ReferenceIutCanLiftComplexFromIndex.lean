/-
This proof composes the uniformization and finite-index polynomial construction
in Oka/Uniformization/{OncePunctured,R3}.lean at 75dcdc3faadd10b986afb9283e89902bcdddecd4
with the core construction in OrbicurveCores/U2/{TheoremG,Assembly}.lean
at 61616dcd77fbe45c083a8ebfa7cc80728f86e841.
-/
import Solutions.Source_ReferenceIutCanLiftComplexAssembly
import Solutions.Source_ReferenceIutCanLiftUniformizationExistence
import Solutions.Source_ReferenceIutCanLiftUniformizationGrowth

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open WeierstrassCurve CanLiftAnalytic
open scoped MatrixGroups

/-- For each nonexceptional complex elliptic curve, finite commensurator index for its
uniformization with the CanLift U1 traces supplies the complex core property. -/
theorem canLift27Complex_of_finite_commensurator_index
    (hIndex : ∀ (E : WeierstrassCurve ℂ) [E.IsElliptic],
      (∀ c ∈ canLiftExceptionalJ, E.j ≠ (c : ℂ)) →
      ∀ (A B : SL(2, ℝ)) (π : ℂ → ℂ × ℂ),
        Matrix.trace ((A * B * A⁻¹ * B⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = -2 →
        Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 →
        IsUniformization E A B π →
        (Subgroup.closure {A, B}).relIndex
          (Subgroup.Commensurable.commensurator (Subgroup.closure {A, B})) ≠ 0) :
    CanLift27Complex := by
  apply canLift27Complex_of_invariant_polynomial_uniformization
  intro E _ hj
  obtain ⟨A, B, π, htrace, htraceA, hπ⟩ := uniformization_oncePunctured E
  have hfin := hIndex E hj A B π htrace htraceA hπ
  exact ⟨A, B, π, hπ,
    hπ.exists_invariant_polynomial_generator_of_finite_commensurator_index hfin⟩

end AbcAdaptation.Reference.Iut.Anabelian
