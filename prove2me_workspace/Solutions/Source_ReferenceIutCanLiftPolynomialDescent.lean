/-
The polynomial descent in Oka/Uniformization/FEtLattice.lean at
75dcdc3faadd10b986afb9283e89902bcdddecd4 of https://github.com/lana-agents/oka
is obtained here from the open mapping theorem on the upper half-plane and
Cauchy's estimate on the descended entire function.
-/
import Solutions.Source_ReferenceIutCanLiftEntirePolynomial
import Solutions.Source_ReferenceIutCanLiftUniformizationCover
import Solutions.Source_ReferenceIutCanLiftPolynomialRigidity
import Solutions.Source_ReferenceIutCanLiftAnalyticCovering
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

open Complex Filter Polynomial Set
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups Topology

variable {W : WeierstrassCurve ℂ} {A B : SL(2, ℝ)} {π : ℂ → ℂ × ℂ}

namespace IsUniformization

/-- Completing the square for the degree-two projection of a Weierstrass curve. -/
theorem equation_iff_partialY_sq (W : WeierstrassCurve ℂ) (x y : ℂ) :
    W.toAffine.Equation x y ↔ complexWeierstrassEquationY W (x, y) ^ 2 = (tq W).eval x := by
  rw [← complexWeierstrassEquation_eq_zero_iff W (x, y), tq_eval]
  unfold complexWeierstrassEquation complexWeierstrassEquationY
    WeierstrassCurve.b₂ WeierstrassCurve.b₄ WeierstrassCurve.b₆
  constructor
  · intro h
    linear_combination 4 * h
  · intro h
    linear_combination h / 4

/-- Every complex number is the first coordinate of a point under the uniformization. -/
theorem surjective_fst (h : IsUniformization W A B π) :
    Function.Surjective fun τ : ℍ ↦ (π τ).1 := by
  intro x
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq ((tq W).eval x) (n := 2) (by decide)
  let y := (r - W.a₁ * x - W.a₃) / 2
  have hY : complexWeierstrassEquationY W (x, y) = r := by
    simp only [complexWeierstrassEquationY, y]
    ring
  have heq := (equation_iff_partialY_sq W x y).mpr (by rw [hY]; exact hr)
  obtain ⟨τ, hτ⟩ := h.surj x y heq
  exact ⟨τ, congrArg Prod.fst hτ⟩

/-- The first coordinate is a quotient map by the open mapping theorem. -/
theorem isQuotientMap_fst (h : IsUniformization W A B π) :
    Topology.IsQuotientMap (fun τ : ℍ ↦ (π τ).1) := by
  let x : ℂ → ℂ := fun w ↦ (π w).1
  have hAna : AnalyticOnNhd ℂ x upperHalfPlaneSet :=
    h.differentiableOn.fst.analyticOnNhd isOpen_upperHalfPlaneSet
  have hopen := (hAna.is_constant_or_isOpen (convex_halfSpace_im_gt 0).isPreconnected).resolve_left
    (by
      rintro ⟨c, hc⟩
      obtain ⟨τ, hτ⟩ := h.surjective_fst (c + 1)
      have he : c + 1 = c := hτ.symm.trans (hc τ τ.im_pos)
      exact one_ne_zero (by linear_combination he))
  have hm : IsOpenMap (fun τ : ℍ ↦ (π τ).1) := by
    intro U hU
    change IsOpen ((x ∘ ((↑) : ℍ → ℂ)) '' U)
    rw [Set.image_comp x ((↑) : ℍ → ℂ) U]
    have himage : ((↑) : ℍ → ℂ) '' U ⊆ upperHalfPlaneSet := by
      rw [← UpperHalfPlane.range_coe]
      exact Set.image_subset_range _ _
    exact hopen _ himage (isOpenEmbedding_coe.isOpenMap U hU)
  exact hm.isQuotientMap
    (continuous_fst.comp (continuous_subtype_val.comp h.continuous_toV)) h.surjective_fst

private theorem differentiableAt_of_fst_pullback (h : IsUniformization W A B π)
    {f : ℍ → ℂ} (hf : HolH f) {F : ℂ → ℂ} (hF : ∀ τ : ℍ, F (π τ).1 = f τ)
    (w : ℂ) (hw : (tq W).eval w ≠ 0) : DifferentiableAt ℂ F w := by
  obtain ⟨τ, hτ⟩ := h.surjective_fst w
  change (π τ).1 = w at hτ
  have hY : complexWeierstrassEquationY W (π τ) ≠ 0 := by
    intro hy
    have he : complexWeierstrassEquationY W (π τ) ^ 2 = (tq W).eval (π τ).1 :=
      (equation_iff_partialY_sq W _ _).mp (h.mem τ)
    rw [hy, zero_pow (by decide : 2 ≠ 0), hτ] at he
    exact hw he.symm
  have hdx : (deriv π τ).1 ≠ 0 := by
    intro hx
    have he := h.equation_deriv τ
    rw [hx, mul_zero, zero_add] at he
    exact (h.holo τ).2 (Prod.ext hx ((mul_eq_zero.mp he).resolve_left hY))
  have hd := h.hasStrictDerivAt_fst τ
  let s := hd.localInverse (fun z ↦ (π z).1) (deriv π τ).1 τ hdx
  have hs0 : s w = (τ : ℂ) := by
    rw [← hτ]
    exact (hd.eventually_left_inverse hdx).self_of_nhds
  have hsd : DifferentiableAt ℂ s w := by
    rw [← hτ]
    exact (hd.to_localInverse hdx).hasDerivAt.differentiableAt
  have hsf : DifferentiableAt ℂ (fun u ↦ f (ofComplex (s u))) w := by
    have hf' : DifferentiableAt ℂ (fun z ↦ f (ofComplex z)) (s w) := by
      rw [hs0]
      exact (hf _ τ.im_pos).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
    exact hf'.comp w hsd
  refine hsf.congr_of_eventuallyEq ?_
  have hsim : ∀ᶠ z in 𝓝 w, 0 < (s z).im :=
    hsd.continuousAt.eventually (by
      rw [hs0]
      exact isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  have hsRight : ∀ᶠ z in 𝓝 w, (π (s z)).1 = z := hτ ▸ hd.eventually_right_inverse hdx
  filter_upwards [hsim, hsRight] with z hz hsz
  rw [← hF (ofComplex (s z)), ofComplex_apply_of_im_pos hz]
  exact (congrArg F hsz).symm

/-- A holomorphic function on the upper half-plane that is constant on the fibers of
the first coordinate and has polynomial growth in that coordinate is a polynomial in it. -/
theorem exists_polynomial_of_fst_fibres (h : IsUniformization W A B π)
    {f : ℍ → ℂ} (hf : HolH f)
    (hfib : ∀ τ τ' : ℍ, (π τ).1 = (π τ').1 → f τ = f τ')
    (hb : PolyBdd (fun τ ↦ (π τ).1) fun τ ↦ ‖f τ‖) :
    ∃ p : ℂ[X], ∀ τ : ℍ, p.eval (π τ).1 = f τ := by
  classical
  choose s hs using h.surjective_fst
  change ∀ z, (π (s z)).1 = z at hs
  let F : ℂ → ℂ := fun z ↦ f (s z)
  have hF (τ : ℍ) : F (π τ).1 = f τ := hfib _ _ (hs _)
  have hcomp : F ∘ (fun τ : ℍ ↦ (π τ).1) = f := funext hF
  have hFc : Continuous F := h.isQuotientMap_fst.continuous_iff.mpr (by
    rw [hcomp]
    exact hf.continuous)
  have hcount : {z : ℂ | (tq W).eval z = 0}.Countable := by
    refine ((tq W).roots.toFinset.finite_toSet.countable).mono ?_
    intro z hz
    exact Multiset.mem_toFinset.mpr ((mem_roots tq_ne_zero).mpr hz)
  have hFd : Differentiable ℂ F := by
    intro z
    exact (Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable (R := 1) (c := z)
      hcount hFc.continuousOn
      (fun w hw ↦ h.differentiableAt_of_fst_pullback hf hF w hw.2)
      (by norm_num)).analyticAt.differentiableAt
  obtain ⟨C, N, hC⟩ := hb
  have hb' (z : ℂ) : ‖F z‖ ≤ |C| * (2 + ‖z‖) ^ N := by
    have hz : ‖F z‖ ≤ C * (2 + ‖(π (s z)).1‖) ^ N := hC (s z)
    rw [hs z] at hz
    exact hz.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  obtain ⟨p, hp⟩ := exists_polynomial_of_entire_growth N hFd (abs_nonneg C) hb'
  exact ⟨p, fun τ ↦ (hp ((π τ).1)).trans (hF τ)⟩

end IsUniformization

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
