/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream files.

Adapted from OrbicurveCores/U2/TheoremG.lean at
61616dcd77fbe45c083a8ebfa7cc80728f86e841 of https://github.com/lana-agents/orbicurve-cores.
-/
import Solutions.Source_ReferenceIutCanLiftAnalyticInput
import Solutions.Source_ReferenceIutCanLiftInvariantCoordinates
import Solutions.Source_ReferenceIutCanLiftMobiusCommensurator

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open WeierstrassCurve CanLiftAnalytic
open JoshiTeich.Act1Scene1.AffineOrbicurvePresentation
open JoshiTeich.ReferenceIut.Anabelian.Genuine
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups

namespace CanLiftAnalytic.IsUniformization

variable {E : WeierstrassCurve ℂ} {G₁ G₂ : SL(2, ℝ)} {π : ℂ → ℂ × ℂ}

private theorem holH_fst (h : IsUniformization E G₁ G₂ π) :
    HolH fun τ : ℍ ↦ (π τ).1 := by
  intro z hz
  refine ((h.holo ⟨z, hz⟩).1.fst.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [isOpen_upper.mem_nhds hz] with w hw
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw]

private theorem holH_snd (h : IsUniformization E G₁ G₂ π) :
    HolH fun τ : ℍ ↦ (π τ).2 := by
  intro z hz
  refine ((h.holo ⟨z, hz⟩).1.snd.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [isOpen_upper.mem_nhds hz] with w hw
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw]

variable [E.IsElliptic]

/-- When the commensurator fixes the first coordinate of a uniformization, every
automorphism of the finite étale algebra fixes the pulled-back normalization coordinate. -/
theorem fixes_normalization_x (h : IsUniformization E G₁ G₂ π)
    (hcomm : ∀ g ∈ Subgroup.Commensurable.commensurator (Subgroup.closure {G₁, G₂}),
      ∀ τ : ℍ, (π ((g • τ : ℍ) : ℂ)).1 = (π τ).1)
    (B : Type) [CommRing B] [Algebra ℂ B] [Algebra (normalizationPresentation E 1 ⊥ false).A B] [IsScalarTower ℂ (normalizationPresentation E 1 ⊥ false).A B]
    [IsDedekindDomain B] [Module.Finite (normalizationPresentation E 1 ⊥ false).A B] [FaithfulSMul (normalizationPresentation E 1 ⊥ false).A B]
    (het : ∀ w : Ideal B, w.IsMaximal → w.ramificationIdx (normalizationPresentation E 1 ⊥ false).A = 1)
    (σ : B ≃ₐ[ℂ] B) :
    σ (algebraMap (normalizationPresentation E 1 ⊥ false).A B (normalizationBaseX E)) = algebraMap (normalizationPresentation E 1 ⊥ false).A B (normalizationBaseX E) := by
  classical
  let A := (normalizationPresentation E 1 ⊥ false).A
  letI : Algebra.FiniteType ℂ B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  letI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  letI : Module.IsTorsionFree A B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      ((faithfulSMul_iff_algebraMap_injective A B).mp inferInstance)
  letI : Module.Flat A B := inferInstance
  let e : E.toAffine.CoordinateRing ≃ₐ[ℂ] A := coordinateBaseNormalizationAlgEquiv E
  let x := normalizationBaseX E
  let y := e (yA E)
  have hxe : e (xA E) = x := coordinateBaseNormalizationAlgEquiv_apply_x E
  let f := coordFun E (fun τ ↦ (π τ).1) (fun τ ↦ (π τ).2) h.mem
  let ι₀ : A →ₐ[ℂ] (ℍ → ℂ) := f.comp e.symm.toAlgHom
  have hf : Function.Injective f :=
    coordFun_injective h.mem fun x₀ y₀ hE ↦ by
      obtain ⟨τ, hτ⟩ := h.surj x₀ y₀ hE
      exact ⟨τ, congrArg Prod.fst hτ, congrArg Prod.snd hτ⟩
  have hinj : Function.Injective ι₀ := hf.comp e.symm.injective
  have hx (τ : ℍ) : ι₀ x τ = (π τ).1 := by
    change f (e.symm x) τ = (π τ).1
    rw [← hxe, e.symm_apply_apply]
    exact coordFun_xA h.mem τ
  have hy (τ : ℍ) : ι₀ y τ = (π τ).2 := by
    change f (e.symm (e (yA E))) τ = (π τ).2
    rw [e.symm_apply_apply]
    exact coordFun_yA h.mem τ
  have hxy (χ χ' : A →ₐ[ℂ] ℂ) (h₁ : χ x = χ' x) (h₂ : χ y = χ' y) : χ = χ' := by
    have h₁' : χ (e (xA E)) = χ' (e (xA E)) := by rwa [hxe]
    have hχ := algHom_ext_coord (χ := χ.comp e.toAlgHom) (χ' := χ'.comp e.toAlgHom) h₁' h₂
    apply AlgHom.ext
    intro a
    obtain ⟨b, rfl⟩ := e.surjective a
    exact AlgHom.congr_fun hχ b
  have hW (χ : A →ₐ[ℂ] ℂ) : E.toAffine.Equation (χ x) (χ y) := by
    rw [← hxe]
    exact equation_coord (χ.comp e.toAlgHom)
  have hhol (a : A) : HolH (ι₀ a) :=
    holH_coordFun h.mem h.holH_fst h.holH_snd (e.symm a)
  have hgrowth (a : A) : PolyBdd (fun τ ↦ (π τ).1) fun τ ↦ ‖ι₀ a τ‖ :=
    polyBdd_coordFun h.mem (e.symm a)
  have hpoly' (g : ℍ → ℂ) (hg : HolH g)
      (hinv : ∀ γ ∈ Subgroup.closure {G₁, G₂}, ∀ τ, g (γ • τ) = g τ)
      (hb : PolyBdd (fun τ ↦ (π τ).1) fun τ ↦ ‖g τ‖) :
      ∃ a, ∀ τ, ι₀ a τ = g τ := by
    obtain ⟨a, ha⟩ := h.exists_coord_of_invariant g hg hinv hb
    refine ⟨e a, fun τ ↦ ?_⟩
    change f (e.symm (e a)) τ = g τ
    rw [e.symm_apply_apply]
    exact ha τ
  let n := Module.finrank A B
  have hcount (τ : ℍ) : Nat.card (Over B (pt ι₀ τ)) = n :=
    EtalePoints.card_points_over het (pt ι₀ τ)
  have hloc (τ : ℍ) : LocPres ι₀ (B := B) n τ :=
    locPres_of_unramified ι₀ (normalizationPresentation E 1 ⊥ false).not_isField het τ
  have hpos : 0 < Nat.card (Over B (pt ι₀ UpperHalfPlane.I)) := by
    rw [hcount]
    exact Module.finrank_pos
  obtain ⟨ψ₀⟩ := (Nat.card_pos_iff.mp hpos).1
  obtain ⟨ι, hι, -, hιh⟩ := exists_isLift hhol hcount hloc UpperHalfPlane.I ψ₀
  obtain ⟨g, hg⟩ := exists_mobius h hx hy hxy hW hhol hcount hloc hgrowth hpoly' hinj σ hι hιh
  have hgc := mobius_mem_commensurator h hx hy hxy hhol hcount hloc σ hι hg
  apply sub_eq_zero.mp
  refine hι.eq_zero hinj fun τ ↦ ?_
  obtain ⟨ψ, hψ⟩ := hι.pt τ
  rw [← hψ, map_sub, hψ, hg, hι.apply_algebraMap, hι.apply_algebraMap, hx, hx]
  exact sub_eq_zero.mpr (hcomm g hgc τ)

end CanLiftAnalytic.IsUniformization

/-- The uniformization form of Theorem G supplies automorphism invariance for covers of
the actual unsigned normalization. -/
theorem canLift27ComplexAutomorphismsFixX_of_uniformization
    (hU : ∀ (E : WeierstrassCurve ℂ) [E.IsElliptic],
      (∀ c ∈ canLiftExceptionalJ, E.j ≠ (c : ℂ)) →
      ∃ (G₁ G₂ : SL(2, ℝ)) (π : ℂ → ℂ × ℂ), IsUniformization E G₁ G₂ π ∧
        (∀ g ∈ Subgroup.Commensurable.commensurator (Subgroup.closure {G₁, G₂}),
          ∀ τ : ℍ, (π ((g • τ : ℍ) : ℂ)).1 = (π τ).1)) :
    CanLift27ComplexAutomorphismsFixX := by
  apply canLift27ComplexAutomorphismsFixX_of_finite_algebra
  intro E _ B _ _ _ _ _ _ _ hj het σ
  obtain ⟨G₁, G₂, π, h, hcomm⟩ := hU E hj
  exact h.fixes_normalization_x hcomm B het σ

end AbcAdaptation.Reference.Iut.Anabelian
