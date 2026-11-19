import Solutions.Source_ReferenceHeightsModularCusp
import Mathlib.Analysis.Complex.OpenMapping

/-!
# Surjectivity of modular `j`

The argument from `Heights/ModularJ.lean` at
`721496ca4c158e511d25d8ccf6bfe8503eda73c1` uses the open mapping theorem
and compactness of the truncated modular fundamental domain.
-/

set_option autoImplicit false

namespace AbcAdaptation.Reference.Heights

open Filter Topology Set UpperHalfPlane
open scoped UpperHalfPlane Manifold

private theorem isOpen_range_modularJ : IsOpen (range modularJ) := by
  let f := modularJ ∘ UpperHalfPlane.ofComplex
  have hanalytic : AnalyticOnNhd ℂ f upperHalfPlaneSet :=
    (UpperHalfPlane.mdifferentiable_iff.mp modularJ_mdifferentiable).analyticOnNhd
      isOpen_upperHalfPlaneSet
  have hconnected : IsPreconnected upperHalfPlaneSet :=
    (Complex.isConnected_of_upperHalfPlane subset_rfl (by grind)).isPreconnected
  have himage : f '' upperHalfPlaneSet = range modularJ := by
    ext w
    constructor
    · rintro ⟨z, _, rfl⟩
      exact ⟨UpperHalfPlane.ofComplex z, rfl⟩
    · rintro ⟨τ, rfl⟩
      exact ⟨(τ : ℂ), τ.im_pos, by simp [f]⟩
  rw [← himage]
  rcases hanalytic.is_constant_or_isOpen hconnected with ⟨w, hconstant⟩ | hopen
  · obtain ⟨τ, hτ⟩ :=
      (modularJ_norm_tendsto_atImInfty.eventually (eventually_gt_atTop ‖w‖)).exists
    have hw : modularJ τ = w := by simpa [f] using hconstant (τ : ℂ) τ.im_pos
    exact False.elim ((lt_irrefl ‖w‖) (hw ▸ hτ))
  · exact hopen upperHalfPlaneSet subset_rfl isOpen_upperHalfPlaneSet

private theorem isClosed_range_modularJ : IsClosed (range modularJ) := by
  apply IsSeqClosed.isClosed
  intro u z hu hlim
  choose v hv using hu
  choose γ hγ using fun n => ModularGroup.exists_smul_mem_fd (v n)
  let τ (n : ℕ) := γ n • v n
  have hfd (n : ℕ) : τ n ∈ ModularGroup.fd := hγ n
  have hj (n : ℕ) : modularJ (τ n) = u n := (modularJ_smul _ _).trans (hv n)
  let r := ‖z‖ + 1
  have hu_bound : ∀ᶠ n in atTop, ‖u n‖ < r :=
    (continuous_norm.continuousAt.tendsto.comp hlim).eventually (Iio_mem_nhds (by simp [r]))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hu_bound
  have hcusp : ∀ᶠ ξ in atImInfty, r < ‖modularJ ξ‖ :=
    modularJ_norm_tendsto_atImInfty.eventually (eventually_gt_atTop r)
  rw [atImInfty, eventually_comap, eventually_atTop] at hcusp
  obtain ⟨y, hy⟩ := hcusp
  have htrunc (n : ℕ) : τ (n + N) ∈ ModularGroup.truncatedFundamentalDomain y := by
    refine ⟨hfd _, ?_⟩
    by_contra h
    have hlarge : r < ‖modularJ (τ (n + N))‖ := hy _ (le_of_not_ge h) _ rfl
    rw [hj] at hlarge
    exact lt_asymm hlarge (hN (n + N) (Nat.le_add_left N n))
  obtain ⟨ξ, _, φ, hφ, hξ⟩ :=
    (ModularGroup.isCompact_truncatedFundamentalDomain y).isSeqCompact htrunc
  use ξ
  have hlimJ := modularJ_mdifferentiable.continuous.continuousAt.tendsto.comp hξ
  have hindex := (tendsto_add_atTop_nat N).comp hφ.tendsto_atTop
  have heq : (fun n => modularJ (τ (φ n + N))) = fun n => u (φ n + N) := funext fun _ => hj _
  change Tendsto (fun n => modularJ (τ (φ n + N))) atTop (𝓝 (modularJ ξ)) at hlimJ
  rw [heq] at hlimJ
  exact tendsto_nhds_unique hlimJ (hlim.comp hindex)

theorem modularJ_surjective : Function.Surjective modularJ := by
  rw [← Set.range_eq_univ]
  exact IsClopen.eq_univ ⟨isClosed_range_modularJ, isOpen_range_modularJ⟩
    ⟨modularJ UpperHalfPlane.I, ⟨UpperHalfPlane.I, rfl⟩⟩

end AbcAdaptation.Reference.Heights
