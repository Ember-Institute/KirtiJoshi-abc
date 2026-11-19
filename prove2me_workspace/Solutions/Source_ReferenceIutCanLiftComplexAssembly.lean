/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream files.

This assembles the uses of Theorem G and rigidity in OrbicurveCores/U2/Assembly.lean
at 61616dcd77fbe45c083a8ebfa7cc80728f86e841 on the level-one normalization models.
-/
import Solutions.Source_ReferenceIutCanLiftFixX
import Solutions.Source_ReferenceIutCanLiftHemiRigid
import Solutions.Source_ReferenceIutCanLiftUnramifiedClosure

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open WeierstrassCurve CanLiftAnalytic
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

end AbcAdaptation.Reference.Iut.Anabelian
