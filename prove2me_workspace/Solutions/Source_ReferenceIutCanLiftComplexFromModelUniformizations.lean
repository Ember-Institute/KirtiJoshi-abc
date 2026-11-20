/-
The classification transport and equal-j rigidity follow OrbicurveCores/S1 at
61616dcd77fbe45c083a8ebfa7cc80728f86e841.
-/
import Solutions.Source_ReferenceIutCanLiftComplexFromArithmetic
import Solutions.Source_ReferenceIutCanLiftTakeuchiRigidity
import Solutions.Source_ReferenceIutCanLiftTakeuchiTransport

set_option autoImplicit false

open scoped MatrixGroups UpperHalfPlane

namespace AbcAdaptation.Reference.Iut.Anabelian

open AbcAdaptation.Reference.Heights
open CanLiftAnalytic CanLiftAnalytic.Fricke CanLiftAnalytic.Takeuchi
open Subgroup.Commensurable (commensurator)

/-- Complex CanLift follows from trace integrality for the actual lattice groups with dense
commensurator and from the uniformizations of the four Takeuchi model curves. -/
theorem canLift27Complex_of_model_uniformizations
    (hInt : ∀ {t : ℍ} (U : LatticeComplementCover (periodPair t)),
      Dense (commensurator (Subgroup.closure {Generators.A U, Generators.B U}) : Set SL(2, ℝ)) →
      ∀ γ ∈ Subgroup.closure {Generators.A U, Generators.B U}, ∃ m : ℤ, tr γ ^ 2 = m)
    (hModels : ∀ k, ∃ i, Uniformizes (ccurve k) (takeuchiPair i) ∨
      Uniformizes ((ccurve k).map (starRingEnd ℂ)) (takeuchiPair i)) :
    CanLift27Complex :=
  canLift27Complex_of_takeuchi hInt uniformizes_takeuchiPair_of_conjugacy
    (fun W W' _ _ _ hW hW' ↦ j_eq_of_uniformizes W W' hW hW') hModels

end AbcAdaptation.Reference.Iut.Anabelian
