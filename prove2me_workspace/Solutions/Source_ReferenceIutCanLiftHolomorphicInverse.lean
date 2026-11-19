/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original path Oka/Uniformization/Holomorphic.lean
-/
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

open Filter Metric Set Topology

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.HolomorphicInverse

/-- A continuous lift of a holomorphic map through a holomorphic map with nonzero derivative is
holomorphic: if `f ∘ σ = g` near `u`, `σ` is continuous at `u`, `f` has nonzero strict derivative
at `σ u` and `g` is differentiable at `u`, then `σ` is differentiable at `u`. -/
theorem differentiableAt_of_comp_eq {f g σ : ℂ → ℂ} {u f' : ℂ}
    (hf : HasStrictDerivAt f f' (σ u)) (hf' : f' ≠ 0) (hσ : ContinuousAt σ u)
    (hfg : ∀ᶠ v in 𝓝 u, f (σ v) = g v) (hg : DifferentiableAt ℂ g u) :
    DifferentiableAt ℂ σ u := by
  have hinv := hf.to_localInverse hf'
  have hleft := hf.eventually_left_inverse hf'
  have hσ' : ∀ᶠ v in 𝓝 u, hf.localInverse f f' (σ u) hf' (f (σ v)) = σ v :=
    hσ.eventually hleft
  have heq : σ =ᶠ[𝓝 u] fun v ↦ hf.localInverse f f' (σ u) hf' (g v) := by
    filter_upwards [hσ', hfg] with v h1 h2
    rw [← h2, h1]
  have hgu : g u = f (σ u) := hfg.self_of_nhds.symm
  have : DifferentiableAt ℂ (fun v ↦ hf.localInverse f f' (σ u) hf' (g v)) u := by
    have h2 : DifferentiableAt ℂ (hf.localInverse f f' (σ u) hf') (g u) := by
      rw [hgu]; exact hinv.hasDerivAt.differentiableAt
    exact h2.comp u hg
  exact this.congr_of_eventuallyEq heq

/-- **Inverse function theorem, section form.** If `f` has a nonzero strict derivative at `a`,
then `f` has a continuous section over a disc about `f a` taking the value `a` at `f a`. -/
theorem exists_localSection {f : ℂ → ℂ} {f' a : ℂ} (hf : HasStrictDerivAt f f' a) (hf' : f' ≠ 0) :
    ∃ ε > 0, ∃ s : ℂ → ℂ, ContinuousOn s (ball (f a) ε) ∧ (∀ y ∈ ball (f a) ε, f (s y) = y) ∧
      s (f a) = a := by
  set e := (hf.hasStrictFDerivAt_equiv hf').toOpenPartialHomeomorph f
  have hsrc : a ∈ e.source := (hf.hasStrictFDerivAt_equiv hf').mem_toOpenPartialHomeomorph_source
  have htgt : f a ∈ e.target :=
    (hf.hasStrictFDerivAt_equiv hf').image_mem_toOpenPartialHomeomorph_target
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp e.open_target _ htgt
  refine ⟨ε, hε, e.symm, e.continuousOn_symm.mono hball, fun y hy ↦ e.right_inv (hball hy), ?_⟩
  exact e.left_inv hsrc

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.HolomorphicInverse
