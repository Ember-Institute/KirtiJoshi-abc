/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original path Oka/Uniformization/R3.lean, the local orders and the first-coordinate
conclusion of le_pmDeck_or.
-/
import Solutions.Source_ReferenceIutCanLiftPolynomialDescent
import Solutions.Source_ReferenceIutCanLiftWeierstrassOrbifoldCount
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

open Complex Filter Polynomial
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups Topology

private theorem analyticOrderAt_polynomial_eval {p : ℂ[X]} (hp : p ≠ 0) (w : ℂ) :
    analyticOrderAt (fun u ↦ p.eval u) w = (rootMultiplicity w p : ℕ) := by
  obtain ⟨q, hq, hqw⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp w
  apply ((Polynomial.differentiable p).analyticAt w).analyticOrderAt_eq_natCast.mpr
  refine ⟨fun u ↦ q.eval u, (Polynomial.differentiable q).analyticAt w, ?_, ?_⟩
  · intro hw
    exact hqw (dvd_iff_isRoot.mpr hw)
  · filter_upwards with u
    conv_lhs => rw [hq]
    simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, smul_eq_mul]

private theorem analyticOrderAt_smul_of_invariant {f : ℂ → ℂ} {g : SL(2, ℝ)}
    (hg : ∀ σ : ℍ, f ((g • σ : ℍ) : ℂ) = f σ) (τ : ℍ) :
    analyticOrderAt (fun z ↦ f z - f ((g • τ : ℍ) : ℂ)) ((g • τ : ℍ) : ℂ) =
      analyticOrderAt (fun z ↦ f z - f τ) τ := by
  let G : ℂ → ℂ := fun z ↦ ((g • ofComplex z : ℍ) : ℂ)
  let g' : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ g
  have hdet : 0 < g'.val.det := by
    change 0 < (Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.mapGL ℝ g)).val
    simp
  have hGa : AnalyticAt ℂ G τ := UpperHalfPlane.analyticAt_smul (g := g') hdet τ
  have hGd : deriv G τ ≠ 0 := UpperHalfPlane.deriv_smul_ne_zero (g := g') hdet τ
  let F : ℂ → ℂ := fun z ↦ f z - f ((g • τ : ℍ) : ℂ)
  have horder := analyticOrderAt_comp_of_deriv_ne_zero (f := F) hGa hGd
  have hGτ : G τ = ((g • τ : ℍ) : ℂ) := by simp only [G, ofComplex_apply]
  rw [hGτ] at horder
  change analyticOrderAt F ((g • τ : ℍ) : ℂ) = _
  rw [← horder]
  apply analyticOrderAt_congr
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
  let σ : ℍ := ⟨z, hz⟩
  have hGσ : G z = ((g • σ : ℍ) : ℂ) := by
    change ((g • ofComplex z : ℍ) : ℂ) = _
    rw [ofComplex_apply_of_im_pos hz]
  change f (G z) - f ((g • τ : ℍ) : ℂ) = f z - f τ
  rw [hGσ, hg σ, hg τ]

namespace IsUniformization

variable {W : WeierstrassCurve ℂ} [W.IsElliptic]
variable {A B : SL(2, ℝ)} {π : ℂ → ℂ × ℂ}

private theorem analyticOrderAt_fst_sub (h : IsUniformization W A B π) (τ : ℍ) :
    analyticOrderAt (fun z ↦ (π z).1 - (π τ).1) τ =
      (hemiMultiplicity (E₂ W) (π τ).1 : ℕ) := by
  let x : ℂ → ℂ := fun z ↦ (π z).1
  let d : ℂ → ℂ := fun z ↦ complexWeierstrassEquationY W (π z)
  have hx : AnalyticAt ℂ x τ :=
    h.differentiableOn.fst.analyticAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  have held (σ : ℍ) : d σ ^ 2 = (tq W).eval (x σ) :=
    (equation_iff_partialY_sq W (x σ) (π σ).2).mp (h.mem σ)
  have hπderiv : complexWeierstrassEquationX W (π τ) * (deriv π τ).1 +
      d τ * (deriv π τ).2 = 0 := h.equation_deriv τ
  change analyticOrderAt (fun z ↦ x z - x τ) τ = (hemiMultiplicity (E₂ W) (x τ) : ℕ)
  unfold hemiMultiplicity
  by_cases hm : x τ ∈ E₂ W
  · rw [if_pos hm]
    change analyticOrderAt (fun z ↦ x z - x τ) τ = 2
    have hroot : x τ ∈ (tq W).roots := Multiset.mem_toFinset.mp hm
    have heval : (tq W).eval (x τ) = 0 := (mem_roots tq_ne_zero).mp hroot
    have hdτ : d τ = 0 := sq_eq_zero_iff.mp ((held τ).trans heval)
    have hFx : complexWeierstrassEquationX W (π τ) ≠ 0 :=
      (h.nonsingular τ).resolve_right (fun hy ↦ hy hdτ)
    rw [hdτ, zero_mul, add_zero] at hπderiv
    have hdx : (deriv π τ).1 = 0 := (mul_eq_zero.mp hπderiv).resolve_left hFx
    have hdy : (deriv π τ).2 ≠ 0 := fun hb ↦ (h.holo τ).2 (Prod.ext hdx hb)
    have hdd :
        HasDerivAt d (2 * (deriv π τ).2 + W.a₁ * (deriv π τ).1) τ := by
      exact
        (((h.hasDerivAt_snd τ).const_mul 2).add
          ((h.hasDerivAt_fst τ).const_mul W.a₁)).add_const W.a₃
    have hdd₀ : deriv d τ ≠ 0 := by
      rw [hdd.deriv, hdx, mul_zero, add_zero]
      exact mul_ne_zero (by norm_num) hdy
    have hdDiff : DifferentiableOn ℂ d upperHalfPlaneSet := by
      exact
        (((h.differentiableOn.snd.const_mul (2 : ℂ)).add
          (h.differentiableOn.fst.const_mul W.a₁)).add_const W.a₃)
    have hd := hdDiff.analyticAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
    have hdo : analyticOrderAt d τ = 1 :=
      hd.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hdτ hdd₀
    have hsq : ((fun u ↦ (tq W).eval u) ∘ x) =ᶠ[𝓝 (τ : ℂ)] d ^ 2 := by
      filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
      exact (held ⟨z, hz⟩).symm
    have hq : analyticOrderAt (fun u ↦ (tq W).eval u) (x τ) = 1 := by
      rw [analyticOrderAt_polynomial_eval tq_ne_zero, ← count_roots]
      simp only [Multiset.count_eq_one_of_mem tq_roots_nodup hroot, Nat.cast_one]
    have hcomp :=
      ((Polynomial.differentiable (tq W)).analyticAt (x τ)).analyticOrderAt_comp hx
    rw [hq, one_mul] at hcomp
    rw [← hcomp, analyticOrderAt_congr hsq, analyticOrderAt_pow hd 2, hdo,
      two_nsmul, one_add_one_eq_two]
  · rw [if_neg hm]
    change analyticOrderAt (fun z ↦ x z - x τ) τ = 1
    have hdτ : d τ ≠ 0 := by
      intro hz
      apply hm
      refine Multiset.mem_toFinset.mpr ((mem_roots tq_ne_zero).mpr ?_)
      change (tq W).eval (x τ) = 0
      rw [← held τ, hz, zero_pow (by decide)]
    have hdx : (deriv π τ).1 ≠ 0 := by
      intro hx₀
      rw [hx₀, mul_zero, zero_add] at hπderiv
      exact (h.holo τ).2 (Prod.ext hx₀ ((mul_eq_zero.mp hπderiv).resolve_left hdτ))
    exact hx.analyticOrderAt_sub_eq_one_of_deriv_ne_zero (by
      change deriv x τ ≠ 0
      rw [(h.hasDerivAt_fst τ).deriv]
      exact hdx)

private theorem analyticOrderAt_polynomial_fst_sub (h : IsUniformization W A B π)
    {s : ℂ[X]} (hs : 0 < s.natDegree) (τ : ℍ) :
    analyticOrderAt (fun z ↦ s.eval (π z).1 - s.eval (π τ).1) τ =
      (polynomialRamificationIdx s (π τ).1 * hemiMultiplicity (E₂ W) (π τ).1 : ℕ) := by
  let x : ℂ → ℂ := fun z ↦ (π z).1
  let p : ℂ[X] := s - C (s.eval (x τ))
  have hpa := (Polynomial.differentiable p).analyticAt (x τ)
  have hxa : AnalyticAt ℂ x τ :=
    h.differentiableOn.fst.analyticAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  have heq : (fun z ↦ s.eval (π z).1 - s.eval (π τ).1) =
      (fun w ↦ p.eval w) ∘ x := by
    funext z
    simp only [p, x, Function.comp_apply, eval_sub, eval_C]
  have hpo : analyticOrderAt (fun w ↦ p.eval w) (x τ) = (polynomialRamificationIdx s (x τ) : ℕ) :=
    analyticOrderAt_polynomial_eval (polynomial_sub_C_ne_zero hs _) _
  rw [heq, hpa.analyticOrderAt_comp hxa, hpo, h.analyticOrderAt_fst_sub, ENat.natCast_mul]

/-- The first coordinate is invariant under a subgroup when a nonconstant invariant
polynomial in that coordinate has the subgroup's orbits as its fibers. -/
theorem fst_smul_eq_of_invariant_polynomial (h : IsUniformization W A B π)
    (hj₀ : W.j ≠ 0) (hj₁₇₂₈ : W.j ≠ 1728) {N : Subgroup SL(2, ℝ)}
    {s : ℂ[X]} (hs : 0 < s.natDegree)
    (hinv : ∀ n ∈ N, ∀ τ : ℍ, s.eval (π ((n • τ : ℍ) : ℂ)).1 = s.eval (π τ).1)
    (htrans : ∀ τ τ' : ℍ, s.eval (π τ).1 = s.eval (π τ').1 → ∃ n ∈ N, n • τ = τ') :
    ∀ n ∈ N, ∀ τ : ℍ, (π ((n • τ : ℍ) : ℂ)).1 = (π τ).1 := by
  have hweighted (w w' : ℂ) (hww' : s.eval w = s.eval w') :
      polynomialRamificationIdx s w * hemiMultiplicity (E₂ W) w =
        polynomialRamificationIdx s w' * hemiMultiplicity (E₂ W) w' := by
    obtain ⟨τ, hτ⟩ := h.surjective_fst w
    obtain ⟨τ', hτ'⟩ := h.surjective_fst w'
    change (π τ).1 = w at hτ
    change (π τ').1 = w' at hτ'
    obtain ⟨n, hnN, hn⟩ := htrans τ τ' (by rwa [hτ, hτ'])
    have horder := analyticOrderAt_smul_of_invariant
      (f := fun z ↦ s.eval (π z).1) (hinv n hnN) τ
    rw [hn, h.analyticOrderAt_polynomial_fst_sub hs τ',
      h.analyticOrderAt_polynomial_fst_sub hs τ, hτ, hτ'] at horder
    exact ENat.natCast_inj.mp horder.symm
  have hsInj := polynomial_eval_injective_of_hemi_orbifold hs hj₀ hj₁₇₂₈ hweighted
  exact fun n hn τ ↦ hsInj (hinv n hn τ)

end IsUniformization

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
