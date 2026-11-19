/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream files.

This assembles the uses of Theorem G and rigidity in OrbicurveCores/U2/Assembly.lean
at 61616dcd77fbe45c083a8ebfa7cc80728f86e841 on the level-one normalization models.
-/
import Solutions.Source_ReferenceIutCanLiftFixX
import Solutions.Source_ReferenceIutCanLiftFirstCoordinateRigidity
import Solutions.Source_ReferenceIutCanLiftHemiRigid
import Solutions.Source_ReferenceIutCanLiftUnramifiedClosure

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open WeierstrassCurve Polynomial CanLiftAnalytic
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups

/-- The commensurator condition on the uniformization gives the complex core theorem. -/
theorem canLift27Complex_of_uniformization
    (hU : ∀ (E : WeierstrassCurve ℂ) [E.IsElliptic],
      (∀ c ∈ canLiftExceptionalJ, E.j ≠ (c : ℂ)) →
      ∃ (G₁ G₂ : SL(2, ℝ)) (π : ℂ → ℂ × ℂ), IsUniformization E G₁ G₂ π ∧
        (∀ g ∈ Subgroup.Commensurable.commensurator (Subgroup.closure {G₁, G₂}),
          ∀ τ : ℍ, (π ((g • τ : ℍ) : ℂ)).1 = (π τ).1)) :
    CanLift27Complex :=
  canLift27Complex_of_xDescends_and_hemiRigid
    (canLift27ComplexXDescends_of_analytic (canLift27ComplexAutomorphismsFixX_of_uniformization hU))
    canLift27ComplexHemiRigid

/-- Invariant polynomials whose fibers are commensurator orbits supply the
first-coordinate condition in the complex core theorem. -/
theorem canLift27Complex_of_invariant_polynomial_uniformization
    (hU : ∀ (E : WeierstrassCurve ℂ) [E.IsElliptic],
      (∀ c ∈ canLiftExceptionalJ, E.j ≠ (c : ℂ)) →
      ∃ (G₁ G₂ : SL(2, ℝ)) (π : ℂ → ℂ × ℂ), IsUniformization E G₁ G₂ π ∧
        ∃ s : ℂ[X], 0 < s.natDegree ∧
          (∀ n ∈ Subgroup.Commensurable.commensurator (Subgroup.closure {G₁, G₂}),
            ∀ τ : ℍ, s.eval (π ((n • τ : ℍ) : ℂ)).1 = s.eval (π τ).1) ∧
          (∀ τ τ' : ℍ, s.eval (π τ).1 = s.eval (π τ').1 →
            ∃ n ∈ Subgroup.Commensurable.commensurator (Subgroup.closure {G₁, G₂}),
              n • τ = τ')) :
    CanLift27Complex := by
  apply canLift27Complex_of_uniformization
  intro E _ hE
  obtain ⟨G₁, G₂, π, hπ, s, hs, hinv, htrans⟩ := hU E hE
  have hj₀ : E.j ≠ 0 := by simpa using hE 0 (by simp [canLiftExceptionalJ])
  have hj₁₇₂₈ : E.j ≠ 1728 := by simpa using hE 1728 (by simp [canLiftExceptionalJ])
  exact ⟨G₁, G₂, π, hπ, hπ.fst_smul_eq_of_invariant_polynomial hj₀ hj₁₇₂₈ hs hinv htrans⟩

end AbcAdaptation.Reference.Iut.Anabelian
