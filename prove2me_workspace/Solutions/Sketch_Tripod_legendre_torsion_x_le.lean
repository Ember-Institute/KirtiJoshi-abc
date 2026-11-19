import Solutions.Source_TripodCyclicArch
import Theorems.Thm_AbcAdaptation_Reference_Heights_exists_torsion_x_bound

set_option autoImplicit false

open AbcAdaptation

theorem solution (c : ℝ) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ Tripod.LegendreTorsionXBound c C₀ :=
  Tripod.legendre_torsion_x_le_of_complex Reference.Heights.exists_torsion_x_bound c
