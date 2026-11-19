/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original path Oka/Uniformization/CoveringLift.lean
-/
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Homotopy.Lifting

set_option autoImplicit false

open Set Function Topology

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

/-- A homeomorphism is a covering map. -/
theorem isCoveringMap_homeomorph {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (e : E ≃ₜ X) : IsCoveringMap e := by
  intro x
  let H : e ⁻¹' univ ≃ₜ ↥(univ : Set X) × PUnit.{1} := ((Homeomorph.Set.univ E).trans e).trans
      ((Homeomorph.Set.univ X).symm.trans (Homeomorph.prodPUnit (univ : Set X)).symm)
  have hU : IsEvenlyCovered e x PUnit.{1} :=
    ⟨inferInstance, univ, mem_univ x, isOpen_univ, isOpen_univ, H, fun y ↦ rfl⟩
  have : Unique (e ⁻¹' {x}) :=
    { default := ⟨e.symm x, by simp⟩
      uniq := fun y ↦ Subtype.ext (by
        have : e y = x := y.2
        simp [← this]) }
  exact hU.of_fiber_homeomorph (Homeomorph.homeomorphOfUnique _ _)

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

/-- **Lifting through a covering, convex source.** Let `f` be a covering on `V`, `D` a convex set
and `g` continuous on `D` with values in `V`. Given `a₀ ∈ D` and `e₀` over `g a₀`, there is a
continuous `σ` on `D` with `f ∘ σ = g` on `D` and `σ a₀ = e₀`. -/
theorem IsCoveringMapOn.exists_lift_of_convex {f : E → X} {V : Set X} (hf : IsCoveringMapOn f V)
    {D : Set F} (hD : Convex ℝ D) {g : F → X} (hg : ContinuousOn g D) (hgV : MapsTo g D V)
    {a₀ : F} (ha₀ : a₀ ∈ D) {e₀ : E} (he₀ : f e₀ = g a₀) :
    ∃ σ : F → E, ContinuousOn σ D ∧ (∀ a ∈ D, f (σ a) = g a) ∧ σ a₀ = e₀ := by
  have : Nonempty D := ⟨⟨a₀, ha₀⟩⟩
  have := hD.contractibleSpace ⟨a₀, ha₀⟩
  have := hD.locallyPathConnectedSpace
  let g' : C(D, X) := ⟨D.domRestrict g, hg.domRestrict⟩
  obtain ⟨F', ⟨hF0, hF⟩, -⟩ := hf.existsUnique_continuousMap_lifts g' (a₀ := ⟨a₀, ha₀⟩) he₀
    fun a ↦ hgV a.2
  classical
  refine ⟨fun a ↦ if h : a ∈ D then F' ⟨a, h⟩ else e₀, ?_, fun a ha ↦ ?_, by simp [ha₀, hF0]⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    convert F'.continuous using 1
    funext a
    simp [a.2]
  · simp only [ha, dite_true]
    exact congrFun hF ⟨a, ha⟩

/-- Two continuous lifts through a covering agree on a preconnected set if they agree at a point
and have the same projection on the set. -/
theorem IsCoveringMapOn.eqOn_of_lift {A : Type*} [TopologicalSpace A]
    {f : E → X} {V : Set X} (hf : IsCoveringMapOn f V) {D : Set A} (hD : IsPreconnected D)
    {σ₁ σ₂ : A → E} (h₁ : ContinuousOn σ₁ D) (h₂ : ContinuousOn σ₂ D)
    (hV : ∀ a ∈ D, f (σ₁ a) ∈ V) (heq : ∀ a ∈ D, f (σ₁ a) = f (σ₂ a))
    {a₀ : A} (ha₀ : a₀ ∈ D) (h₀ : σ₁ a₀ = σ₂ a₀) : EqOn σ₁ σ₂ D := by
  have : PreconnectedSpace D := Subtype.preconnectedSpace hD
  let τ₁ : D → f ⁻¹' V := fun a ↦ ⟨σ₁ a, hV a a.2⟩
  let τ₂ : D → f ⁻¹' V := fun a ↦ ⟨σ₂ a, by
    change f (σ₂ ↑a) ∈ V
    rw [← heq a a.2]
    exact hV a a.2⟩
  have hτ₁ : Continuous τ₁ := h₁.domRestrict.subtype_mk _
  have hτ₂ : Continuous τ₂ := h₂.domRestrict.subtype_mk _
  have hcomp : V.restrictPreimage f ∘ τ₁ = V.restrictPreimage f ∘ τ₂ := by
    funext a
    exact Subtype.ext (heq a a.2)
  have hh : τ₁ = τ₂ := hf.isCoveringMap_restrictPreimage.eq_of_comp_eq hτ₁ hτ₂ hcomp
    ⟨a₀, ha₀⟩ (Subtype.ext h₀)
  intro a ha
  exact congrArg Subtype.val (congrFun hh ⟨a, ha⟩)
