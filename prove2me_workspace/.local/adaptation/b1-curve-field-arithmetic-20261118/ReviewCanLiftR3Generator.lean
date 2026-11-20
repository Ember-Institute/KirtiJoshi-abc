import ArithmeticTeichmullerSpaces.Prologue.Audit.Checks
import ArithmeticTeichmullerSpaces.Prologue.Audit.ImportAudit
import ArithmeticTeichmullerSpaces.Act1Scene1
import ArithmeticTeichmullerSpaces.Prologue.Audit.AxiomAudit
import Solutions.Source_ReferenceIutCanLiftFirstCoordinateRigidity
import Solutions.Source_ReferenceIutCanLiftInvariantPolynomialGenerator

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

open UpperHalfPlane
open scoped MatrixGroups

#print axioms exists_coset_polynomial
#print axioms IsUniformization.exists_orbit_separating_polynomials
#print axioms RatFuncPoly.exists_poly_generator
#print axioms IsUniformization.exists_fst_fibre_group
#print axioms IsUniformization.exists_invariant_polynomial_generator_for_commensurator

example {W : WeierstrassCurve ℂ} [W.IsElliptic] {A B : SL(2, ℝ)} {π : ℂ → ℂ × ℂ}
    (h : IsUniformization W A B π) (hj₀ : W.j ≠ 0) (hj₁₇₂₈ : W.j ≠ 1728)
    (hfin : (Subgroup.closure {A, B}).relIndex
      (Subgroup.Commensurable.commensurator (Subgroup.closure {A, B})) ≠ 0)
    (hb : ∀ g ∈ Subgroup.Commensurable.commensurator (Subgroup.closure {A, B}),
      PolyBdd (fun τ : ℍ ↦ (π τ).1) fun τ ↦ ‖(π (g • τ : ℍ)).1‖) :
    ∀ g ∈ Subgroup.Commensurable.commensurator (Subgroup.closure {A, B}),
      ∀ τ : ℍ, (π (g • τ : ℍ)).1 = (π τ).1 := by
  obtain ⟨s, hs, hsinv, hsfib⟩ := h.exists_invariant_polynomial_generator_for_commensurator hfin hb
  exact h.fst_smul_eq_of_invariant_polynomial hj₀ hj₁₇₂₈ hs hsinv hsfib

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
