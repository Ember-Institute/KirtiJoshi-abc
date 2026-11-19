import Solutions.Source_ReferenceHeightsLatticePointMapAddition
import Solutions.Source_ReferenceHeightsModularComparisons
import Solutions.Source_ReferenceHeightsModularRange
import Solutions.Source_ReferenceHeightsTorsionArchimedean

set_option autoImplicit false

namespace AbcAdaptation.Reference.Heights

/-- General complex torsion bound from `Heights/TorsionArchimedean.lean` at
`721496ca4c158e511d25d8ccf6bfe8503eda73c1`. -/
theorem exists_torsion_x_bound_from_source : Tripod.ComplexTorsionXBound :=
  complexTorsionXBound_of_modular modularJ_surjective latticePointUniformization
    modularDeltaJ_fd_comparison modularIm_logLogJ_fd_comparison

end AbcAdaptation.Reference.Heights

namespace AbcAdaptation.Tripod

/-- The Legendre specialization from `Iut/Tripod/CyclicArch.lean` at
`07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`. -/
theorem legendre_torsion_x_le_from_source (c : ℝ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ LegendreTorsionXBound c C₀ :=
  legendre_torsion_x_le_of_complex Reference.Heights.exists_torsion_x_bound_from_source c

end AbcAdaptation.Tripod
