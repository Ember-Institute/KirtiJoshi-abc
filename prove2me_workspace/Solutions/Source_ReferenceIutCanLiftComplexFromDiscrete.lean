/-
The discrete overgroup argument and uniformization transport follow
OrbicurveCores/Fuchsian/Covolume.lean and OrbicurveCores/U2/R3.lean at
61616dcd77fbe45c083a8ebfa7cc80728f86e841. The lattice model comes from
Oka/Uniformization/OncePunctured.lean at 75dcdc3faadd10b986afb9283e89902bcdddecd4.
-/
import Solutions.Source_ReferenceIutCanLiftComplexFromIndex
import Solutions.Source_ReferenceIutCanLiftDiscreteOvergroupIndex

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open AbcAdaptation.Reference.Heights
open CanLiftAnalytic WeierstrassCurve
open Subgroup.Commensurable (commensurator)
open scoped UpperHalfPlane

/-- Discreteness of the lattice commensurator for each nonexceptional complex elliptic
curve supplies the finite index needed for the complex core property. -/
theorem canLift27Complex_of_discrete_lattice_commensurator
    (hDiscrete : ∀ (E : WeierstrassCurve ℂ) [E.IsElliptic],
      (∀ c ∈ canLiftExceptionalJ, E.j ≠ (c : ℂ)) →
      ∀ (t : ℍ) (C : VariableChange ℂ), C • latticeCurve t = E →
        let U := latticeComplementCover (periodPair t)
        DiscreteTopology (commensurator (Subgroup.closure {Generators.A U, Generators.B U}))) :
    CanLift27Complex := by
  apply canLift27Complex_of_finite_commensurator_index
  intro E _ hj A B π _ _ hπ
  obtain ⟨t, C, hC⟩ := exists_variableChange_latticeCurve E
  let U := latticeComplementCover (periodPair t)
  have hU : IsUniformization E (Generators.A U) (Generators.B U)
      (latticeParameterization t C ∘ U.Ψ) := by
    rw [← hC]
    exact U.uniformizes C (Generators.deckGroup_eq_pmGroup U)
  haveI : DiscreteTopology (commensurator (Subgroup.closure {Generators.A U, Generators.B U})) :=
    hDiscrete E hj t C hC
  exact (hU.relIndex_commensurator_ne_zero_iff_of_uniformization hπ).mp
    (Peripheral.closure_relIndex_commensurator_ne_zero_of_discrete U)

end AbcAdaptation.Reference.Iut.Anabelian
