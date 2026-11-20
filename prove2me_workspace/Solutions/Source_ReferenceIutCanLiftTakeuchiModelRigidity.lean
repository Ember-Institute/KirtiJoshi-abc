/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/S1/Main.lean, lines 104–128
-/
import Solutions.Source_ReferenceIutCanLiftTakeuchiModelCurves
import Solutions.Source_ReferenceIutCanLiftUniformizationCover
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Choose

set_option autoImplicit false

open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi

/-- The matrix pair uniformizes the punctured curve if a uniformizing map exists. -/
abbrev Uniformizes (W : WeierstrassCurve ℂ) (pair : SL(2, ℝ) × SL(2, ℝ)) : Prop :=
  ∃ π : ℂ → ℂ × ℂ, IsUniformization W pair.1 pair.2 π

/-- If each model is uniformized by a classified pair, rigidity assigns a different
pair index to each model. Every curve uniformized by a classified pair, possibly
after complex conjugation, then has exceptional `j`. -/
theorem exceptionalJ_of_model_uniformizations
    (pairs : Fin 4 → SL(2, ℝ) × SL(2, ℝ))
    (hRigid : ∀ (W W' : WeierstrassCurve ℂ) [W.IsElliptic] [W'.IsElliptic] (i : Fin 4),
      Uniformizes W (pairs i) → Uniformizes W' (pairs i) → W.j = W'.j)
    (hModels : ∀ k, ∃ i, Uniformizes (ccurve k) (pairs i) ∨
      Uniformizes ((ccurve k).map (starRingEnd ℂ)) (pairs i))
    (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (hW : ∃ i, Uniformizes W (pairs i) ∨ Uniformizes (W.map (starRingEnd ℂ)) (pairs i)) :
    ∃ c ∈ canLiftExceptionalJ, W.j = (c : ℂ) := by
  classical
  have hCovers (k : Fin 4) : ∃ i, Uniformizes (ccurve k) (pairs i) := by
    simpa only [ccurve_conj, or_self] using hModels k
  choose classOf hClass using hCovers
  have hInjective : Function.Injective classOf := by
    intro k l h
    have hl : Uniformizes (ccurve l) (pairs (classOf k)) := by
      rw [h]
      exact hClass l
    apply qj_injective
    apply Rat.cast_injective (α := ℂ)
    simpa only [ccurve_j] using hRigid (ccurve k) (ccurve l) (classOf k) (hClass k) hl
  obtain ⟨i, hi⟩ := hW
  obtain ⟨k, rfl⟩ := Finite.surjective_of_injective hInjective i
  refine ⟨qj k, qj_mem k, ?_⟩
  rcases hi with hDirect | hConj
  · rw [← ccurve_j]
    exact hRigid W (ccurve k) (classOf k) hDirect (hClass k)
  · have hj := hRigid (W.map (starRingEnd ℂ)) (ccurve k) (classOf k) hConj (hClass k)
    rw [WeierstrassCurve.map_j, ccurve_j] at hj
    have h := congrArg (starRingEnd ℂ) hj
    simpa only [Complex.conj_conj, map_ratCast] using h

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi
