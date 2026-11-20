/-
This assembly follows OrbicurveCores/{M2/Final,S1/Main,U2/TheoremG}.lean at
61616dcd77fbe45c083a8ebfa7cc80728f86e841.
-/
import Solutions.Source_ReferenceIutCanLiftComplexFromIndex
import Solutions.Source_ReferenceIutCanLiftDenseCommensurator
import Solutions.Source_ReferenceIutCanLiftNielsenDescent
import Solutions.Source_ReferenceIutCanLiftTakeuchiFourGroups
import Solutions.Source_ReferenceIutCanLiftTakeuchiModelRigidity

set_option autoImplicit false

open scoped MatrixGroups UpperHalfPlane

namespace AbcAdaptation.Reference.Iut.Anabelian

open AbcAdaptation.Reference.Heights
open CanLiftAnalytic CanLiftAnalytic.Fricke CanLiftAnalytic.Takeuchi WeierstrassCurve
open Subgroup.Commensurable (commensurator)
open Matrix.SpecialLinearGroup (toGL)

/-- Dense-commensurator trace integrality and the uniformizations of the four Takeuchi
models suffice for complex CanLift, using the signed change of generators and rigidity
of the uniformizations at a fixed classified pair. -/
theorem canLift27Complex_of_takeuchi
    (hInt : ∀ {t : ℍ} (U : LatticeComplementCover (periodPair t)),
      Dense (commensurator (Subgroup.closure {Generators.A U, Generators.B U}) : Set SL(2, ℝ)) →
      ∀ γ ∈ Subgroup.closure {Generators.A U, Generators.B U}, ∃ m : ℤ, tr γ ^ 2 = m)
    (hTransport : ∀ (E : WeierstrassCurve ℂ) [E.IsElliptic] (A B A' B' : SL(2, ℝ)),
      Uniformizes E (A, B) →
      Subgroup.closure {A', B'} = Subgroup.closure {A, B} →
      ∀ (i : Fin 4) (A'' B'' : SL(2, ℝ)), A'' ∈ ({A', -A'} : Set SL(2, ℝ)) →
      B'' ∈ ({B', -B'} : Set SL(2, ℝ)) →
      ∀ g : GL (Fin 2) ℝ, g * toGL A'' * g⁻¹ = toGL (takeuchiPair i).1 →
      g * toGL B'' * g⁻¹ = toGL (takeuchiPair i).2 →
      Uniformizes E (takeuchiPair i) ∨ Uniformizes (E.map (starRingEnd ℂ)) (takeuchiPair i))
    (hRigid : ∀ (W W' : WeierstrassCurve ℂ) [W.IsElliptic] [W'.IsElliptic] (i : Fin 4),
      Uniformizes W (takeuchiPair i) → Uniformizes W' (takeuchiPair i) → W.j = W'.j)
    (hModels : ∀ k, ∃ i, Uniformizes (ccurve k) (takeuchiPair i) ∨
      Uniformizes ((ccurve k).map (starRingEnd ℂ)) (takeuchiPair i)) :
    CanLift27Complex := by
  apply canLift27Complex_of_finite_commensurator_index
  intro E _ hj A B π _ _ hπ
  obtain ⟨t, C, hC⟩ := exists_variableChange_latticeCurve E
  let U := latticeComplementCover (periodPair t)
  have hU : IsUniformization E (Generators.A U) (Generators.B U)
      (latticeParameterization t C ∘ U.Ψ) := by
    rw [← hC]
    exact U.uniformizes C (Generators.deckGroup_eq_pmGroup U)
  apply (hU.relIndex_commensurator_ne_zero_iff_of_uniformization hπ).mp
  intro hInfinite
  have hDense := Peripheral.closure_commensurator_dense_of_relIndex_eq_zero U hInfinite
  obtain ⟨A', B', hSubgroup, hComm, hTraces⟩ :=
    takeuchi_one_infty_of_int (Peripheral.trace_commutator U) (Peripheral.trace_A_ne_zero U)
      (hInt U hDense)
  obtain ⟨i, A'', hA'', B'', hB'', g, hA, hB⟩ := exists_conj_of_takeuchiSq hComm hTraces
  obtain ⟨c, hc, hEq⟩ := exceptionalJ_of_model_uniformizations takeuchiPair hRigid hModels E
    ⟨i, hTransport E _ _ A' B' ⟨_, hU⟩ hSubgroup i A'' B'' hA'' hB'' g hA hB⟩
  exact hj c hc hEq

end AbcAdaptation.Reference.Iut.Anabelian
