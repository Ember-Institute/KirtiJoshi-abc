/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the upstream files.

This adapts Oka/Uniformization/FEtLattice.lean at 75dcdc3faadd10b986afb9283e89902bcdddecd4
of https://github.com/lana-agents/oka. The even and odd parts descend along the actual
affine Weierstrass projection, using the local covering and polynomial descent.
-/
import Solutions.Source_ReferenceIutCanLiftPolynomialDescent
import Solutions.Source_ReferenceIutCanLiftEtaleCoordinates
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

open Complex Filter Polynomial Set
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups Topology

variable {W : WeierstrassCurve ℂ} {A B : SL(2, ℝ)} {π : ℂ → ℂ × ℂ}

private theorem pullback_holH {f : ℂ → ℂ}
    (hf : ∀ τ : ℍ, DifferentiableAt ℂ f τ) : HolH (fun τ ↦ f τ) := by
  intro z hz
  refine ((hf ⟨z, hz⟩).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
  rw [ofComplex_apply_of_im_pos hw]

private theorem HolH.comp_holomorphicH {g : ℍ → ℂ} (hg : HolH g) {T : ℍ → ℍ}
    (hT : HolomorphicH T) : HolH fun τ ↦ g (T τ) := by
  unfold HolH HolomorphicH at *
  have hmaps : MapsTo (fun z : ℂ ↦ (T (ofComplex z) : ℂ)) upperHalfPlaneSet upperHalfPlaneSet :=
    fun z _ ↦ (T (ofComplex z)).im_pos
  refine (hg.comp hT hmaps).congr fun z _ ↦ ?_
  simp only [Function.comp_apply, ofComplex_apply]

namespace IsUniformization

variable [W.IsElliptic]

/-- Weierstrass negation lifts to a holomorphic map of the upper half-plane. -/
theorem exists_lift_neg (h : IsUniformization W A B π) :
    ∃ T : ℍ → ℍ, HolomorphicH T ∧
      ∀ τ : ℍ, π (T τ) = ((π τ).1, W.toAffine.negY (π τ).1 (π τ).2) := by
  let πneg : ℂ → ℂ × ℂ := fun z ↦ ((π z).1, W.toAffine.negY (π z).1 (π z).2)
  have hπneg (τ : ℍ) : DifferentiableAt ℂ πneg τ := by
    have hd := (h.holo τ).1
    exact hd.fst.prodMk ((hd.snd.neg.sub (hd.fst.const_mul _)).sub_const _)
  let q : ℍ → V W := fun τ ↦ ⟨πneg τ, (W.toAffine.equation_neg _ _).mpr (h.mem τ)⟩
  have hcd : DifferentiableOn ℂ πneg upperHalfPlaneSet := fun z hz ↦
    (hπneg ⟨z, hz⟩).differentiableWithinAt
  have hc : Continuous q :=
    (hcd.continuousOn.comp_continuous continuous_coe fun τ ↦ τ.im_pos).subtype_mk _
  let o := UpperHalfPlane.I
  obtain ⟨τ₀, hτ₀⟩ := h.surj (q o).1.1 (q o).1.2 (q o).2
  obtain ⟨T, ⟨-, hT⟩, -⟩ := h.isCoveringMap.existsUnique_continuousMap_lifts
    ⟨q, hc⟩ o τ₀ (Subtype.ext hτ₀)
  have hTπ (τ : ℍ) : π (T τ) = πneg τ :=
    congrArg (fun p : V W ↦ p.1) (congrFun hT τ)
  exact ⟨T, h.holomorphicH_of_lift hπneg T.continuous hTπ, hTπ⟩

private theorem partialY_neg (W : WeierstrassCurve ℂ) (x y : ℂ) :
    complexWeierstrassEquationY W (x, W.toAffine.negY x y) =
      -complexWeierstrassEquationY W (x, y) := by
  unfold complexWeierstrassEquationY WeierstrassCurve.Affine.negY
  ring

/-- Holomorphic functions constant on the uniformization fibers and of polynomial growth
in the first coordinate are evaluations of affine coordinate ring elements. -/
theorem exists_coord_of_invariant (h : IsUniformization W A B π) (g : ℍ → ℂ) (hg : HolH g)
    (hinv : ∀ γ ∈ Subgroup.closure {A, B}, ∀ τ, g (γ • τ) = g τ)
    (hb : PolyBdd (fun τ ↦ (π τ).1) fun τ ↦ ‖g τ‖) :
    ∃ a : W.toAffine.CoordinateRing, ∀ τ : ℍ,
      coordFun W (fun σ ↦ (π σ).1) (fun σ ↦ (π σ).2) h.mem a τ = g τ := by
  classical
  let x : ℍ → ℂ := fun τ ↦ (π τ).1
  let y : ℍ → ℂ := fun τ ↦ (π τ).2
  let d : ℍ → ℂ := fun τ ↦ complexWeierstrassEquationY W (π τ)
  have hdsq (τ : ℍ) : d τ ^ 2 = (tq W).eval (x τ) :=
    (equation_iff_partialY_sq W _ _).mp (h.mem τ)
  obtain ⟨T, hT, hTπ⟩ := h.exists_lift_neg
  have hTx (τ : ℍ) : x (T τ) = x τ := by
    change (π (T τ)).1 = (π τ).1
    rw [hTπ τ]
  have hTT (τ : ℍ) : π (T (T τ)) = π τ := by
    rw [hTπ, hTπ]
    exact Prod.ext rfl (W.toAffine.negY_negY _ _)
  have hflip {τ σ : ℍ} (he : π τ = π σ) : π (T τ) = π (T σ) := by rw [hTπ, hTπ, he]
  have hfib {τ σ : ℍ} (he : π τ = π σ) : g τ = g σ := by
    obtain ⟨γ, hγ, hγτ⟩ := (h.fibre τ σ).mp he
    exact ((congrArg g hγτ).symm.trans (hinv γ hγ τ)).symm
  have hpair (τ σ : ℍ) (hx : x τ = x σ) :
      (g τ = g σ ∧ g (T τ) = g (T σ) ∧ d τ = d σ) ∨
      (g τ = g (T σ) ∧ g (T τ) = g σ ∧ d τ = -d σ) := by
    rcases WeierstrassCurve.Affine.Y_eq_of_X_eq (h.mem τ) (h.mem σ) hx with hy | hy
    · have hEq : π τ = π σ := Prod.ext hx hy
      exact Or.inl ⟨hfib hEq, hfib (hflip hEq), congrArg (complexWeierstrassEquationY W) hEq⟩
    · have hEq : π τ = π (T σ) := by
        rw [hTπ σ]
        exact Prod.ext hx hy
      refine Or.inr ⟨hfib hEq, hfib ((hflip hEq).trans (hTT σ)), ?_⟩
      change complexWeierstrassEquationY W (π τ) = -complexWeierstrassEquationY W (π σ)
      rw [hEq, hTπ, partialY_neg]
  let gp : ℍ → ℂ := fun τ ↦ g τ + g (T τ)
  let gm : ℍ → ℂ := fun τ ↦ (g τ - g (T τ)) * d τ
  have hfibP (τ σ : ℍ) (hx : x τ = x σ) : gp τ = gp σ := by
    rcases hpair τ σ hx with ⟨h₁, h₂, -⟩ | ⟨h₁, h₂, -⟩
    · simp only [gp, h₁, h₂]
    · rw [show gp τ = g τ + g (T τ) from rfl, h₁, h₂, add_comm]
  have hfibM (τ σ : ℍ) (hx : x τ = x σ) : gm τ = gm σ := by
    rcases hpair τ σ hx with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩
    · simp only [gm, h₁, h₂, h₃]
    · simp only [gm, h₁, h₂, h₃]
      ring
  have hgd : HolH (fun τ ↦ g (T τ)) := hg.comp_holomorphicH hT
  have hd : HolH d := pullback_holH fun τ ↦ by
    have hdπ := (h.holo τ).1
    exact ((hdπ.snd.const_mul 2).add (hdπ.fst.const_mul W.a₁)).add_const W.a₃
  have hgp : HolH gp := DifferentiableOn.add hg hgd
  have hgm : HolH gm := DifferentiableOn.mul (DifferentiableOn.sub hg hgd) hd
  have hbT : PolyBdd x fun τ ↦ ‖g (T τ)‖ := by
    obtain ⟨C, N, hC⟩ := hb
    refine ⟨C, N, fun τ ↦ ?_⟩
    have ht : ‖g (T τ)‖ ≤ C * (2 + ‖x (T τ)‖) ^ N := hC (T τ)
    rwa [hTx] at ht
  have hbP : PolyBdd x fun τ ↦ ‖gp τ‖ := (hb.add hbT).mono fun τ ↦ norm_add_le _ _
  have hbD : PolyBdd x fun τ ↦ ‖d τ‖ := by
    refine ((PolyBdd.const 1).add (PolyBdd.poly_eval (tq W))).mono fun τ ↦ ?_
    have hnorm : ‖d τ‖ ^ 2 = ‖(tq W).eval (x τ)‖ := by rw [← norm_pow, hdsq]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖d τ‖ - 1), norm_nonneg ((tq W).eval (x τ))]
  have hbM : PolyBdd x fun τ ↦ ‖gm τ‖ := by
    have hsub : PolyBdd x fun τ ↦ ‖g τ - g (T τ)‖ :=
      (hb.add hbT).mono fun τ ↦ norm_sub_le _ _
    exact (hsub.mul hbD (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)).mono
      fun τ ↦ by simp only [gm, Pi.mul_apply, norm_mul, le_refl]
  obtain ⟨P, hP⟩ := h.exists_polynomial_of_fst_fibres hgp hfibP hbP
  obtain ⟨Q, hQ⟩ := h.exists_polynomial_of_fst_fibres hgm hfibM hbM
  have hdiv : tq W ∣ Q := by
    by_cases hQ0 : Q = 0
    · rw [hQ0]
      exact dvd_zero _
    have hle : (tq W).roots ≤ Q.roots := (Multiset.le_iff_subset tq_roots_nodup).mpr fun e he ↦ by
      have heval : (tq W).eval e = 0 := (mem_roots tq_ne_zero).mp he
      obtain ⟨τ, hτ⟩ := h.surjective_fst e
      have hd₀ : d τ = 0 := by
        have hs := hdsq τ
        rw [show x τ = e from hτ, heval] at hs
        exact sq_eq_zero_iff.mp hs
      apply (mem_roots hQ0).mpr
      rw [IsRoot, ← hτ, hQ]
      simp [gm, hd₀]
    exact (IsAlgClosed.splits _).dvd_of_roots_le_roots tq_ne_zero hle
  obtain ⟨R, hR⟩ := hdiv
  have hodd (τ : ℍ) : g τ - g (T τ) = d τ * R.eval (x τ) := by
    by_cases hd₀ : d τ = 0
    · have hEq : π (T τ) = π τ := by
        rw [hTπ]
        apply Prod.ext
        · rfl
        · change W.toAffine.negY (π τ).1 (π τ).2 = (π τ).2
          unfold WeierstrassCurve.Affine.negY
          change 2 * (π τ).2 + W.a₁ * (π τ).1 + W.a₃ = 0 at hd₀
          linear_combination -hd₀
      rw [hfib hEq, sub_self, hd₀, zero_mul]
    · apply mul_right_cancel₀ hd₀
      calc
        (g τ - g (T τ)) * d τ = Q.eval (x τ) := (hQ τ).symm
        _ = (d τ * R.eval (x τ)) * d τ := by
          rw [hR, eval_mul, ← hdsq]
          ring
  let S := C (1 / 2 : ℂ) * (P + (C W.a₁ * X + C W.a₃) * R)
  refine ⟨S • (1 : W.toAffine.CoordinateRing) + R • yA W, fun τ ↦ ?_⟩
  rw [coordFun_smul_basis]
  change S.eval (x τ) + R.eval (x τ) * y τ = g τ
  calc
    _ = (P.eval (x τ) + d τ * R.eval (x τ)) / 2 := by
      simp only [S, d, y, eval_mul, eval_add, eval_C, eval_X, complexWeierstrassEquationY]
      ring
    _ = g τ := by
      rw [← hodd]
      rw [show P.eval (x τ) = gp τ from hP τ]
      unfold gp
      ring

end IsUniformization

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
