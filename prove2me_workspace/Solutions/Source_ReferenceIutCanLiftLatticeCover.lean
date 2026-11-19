/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original paths Oka/Uniformization/{LatticeComplement,DeckGroup}.lean
-/
import Solutions.Source_ReferenceIutCanLiftCayley
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Topology.Covering.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Complex Metric Set
open UpperHalfPlane hiding I I_re I_im
open scoped UpperHalfPlane

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

/-- A holomorphic covering of the complement of a period lattice by the upper half-plane. -/
structure LatticeComplementCover (L : PeriodPair) where
  Ψ : ℂ → ℂ
  covering : IsCoveringMapOn (fun τ : ℍ ↦ Ψ τ) (L.lattice : Set ℂ)ᶜ
  notMem : ∀ z : ℂ, 0 < z.im → Ψ z ∉ L.lattice
  differentiableOn : DifferentiableOn ℂ Ψ {z | 0 < z.im}
  deriv_ne_zero : ∀ z : ℂ, 0 < z.im → deriv Ψ z ≠ 0
  surj : ∀ w ∉ L.lattice, ∃ τ : ℍ, Ψ τ = w

namespace LatticeComplementCover

variable {L : PeriodPair}

/-- The restriction of the lattice-complement covering map to the upper half-plane. -/
def ψ (U : LatticeComplementCover L) (τ : ℍ) : ℂ := U.Ψ τ

theorem ψ_notMem (U : LatticeComplementCover L) (τ : ℍ) : U.ψ τ ∉ L.lattice :=
  U.notMem τ τ.im_pos

theorem continuous_ψ (U : LatticeComplementCover L) : Continuous U.ψ :=
  U.differentiableOn.continuousOn.comp_continuous continuous_coe fun τ ↦ τ.im_pos

theorem holo (U : LatticeComplementCover L) (τ : ℍ) :
    DifferentiableAt ℂ U.Ψ τ ∧ deriv U.Ψ τ ≠ 0 :=
  ⟨U.differentiableOn.differentiableAt (isOpen_upper.mem_nhds τ.im_pos),
    U.deriv_ne_zero τ τ.im_pos⟩

private theorem deriv_cayley_ne_zero {z : ℂ} (hz : 0 < z.im) : deriv cayley z ≠ 0 := by
  have hd := ((hasDerivAt_id z).sub_const I).fun_div
    ((hasDerivAt_id z).add_const I) (add_I_ne_zero hz)
  change HasDerivAt cayley ((1 * (z + I) - (z - I) * 1) / (z + I) ^ 2) z at hd
  rw [hd.deriv, show 1 * (z + I) - (z - I) * 1 = 2 * I by ring]
  exact div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ (add_I_ne_zero hz))

/-- Transport a covering of the lattice complement from the unit disc to the upper half-plane. -/
noncomputable def of_disc (f : ℂ → ℂ)
    (hcov : IsCoveringMapOn f (L.lattice : Set ℂ)ᶜ)
    (hpre : f ⁻¹' (L.lattice : Set ℂ)ᶜ = ball 0 1)
    (hd : DifferentiableOn ℂ f (ball 0 1))
    (hderiv : ∀ z ∈ ball (0 : ℂ) 1, deriv f z ≠ 0)
    (hsurj : SurjOn f (ball 0 1) (L.lattice : Set ℂ)ᶜ) :
    LatticeComplementCover L := by
  let Ψ := f ∘ cayley
  have hnotMem (z : ℂ) (hz : 0 < z.im) : Ψ z ∉ L.lattice := by
    change cayley z ∈ f ⁻¹' (L.lattice : Set ℂ)ᶜ
    rw [hpre]
    exact cayley_mem_ball hz
  refine
    { Ψ := Ψ
      covering := ?_
      notMem := hnotMem
      differentiableOn := hd.comp differentiableOn_cayley fun _ hz ↦ cayley_mem_ball hz
      deriv_ne_zero := ?_
      surj := ?_ }
  · let e : ℍ ≃ₜ f ⁻¹' (L.lattice : Set ℂ)ᶜ :=
      { toFun := fun τ ↦ ⟨cayley τ, by rw [hpre]; exact cayley_mem_ball τ.im_pos⟩
        invFun := fun w ↦ ⟨cayleyInv w, im_cayleyInv_pos (hpre ▸ w.2)⟩
        left_inv := fun τ ↦ UpperHalfPlane.ext (cayleyInv_cayley τ.im_pos)
        right_inv := fun w ↦ Subtype.ext (cayley_cayleyInv (hpre ▸ w.2))
        continuous_toFun := by
          refine Continuous.subtype_mk ?_ _
          exact differentiableOn_cayley.continuousOn.comp_continuous continuous_coe
            fun τ ↦ τ.im_pos
        continuous_invFun := by
          refine isOpenEmbedding_coe.isInducing.continuous_iff.mpr ?_
          change Continuous fun w : f ⁻¹' (L.lattice : Set ℂ)ᶜ ↦ cayleyInv w
          exact differentiableOn_cayleyInv.continuousOn.comp_continuous continuous_subtype_val
            fun w ↦ hpre ▸ w.2 }
    exact IsCoveringMapOn.of_isCoveringMap_subtype L.isClosed_lattice.isOpen_compl
      (fun τ ↦ hnotMem τ τ.im_pos) (hcov.isCoveringMap_restrictPreimage.comp_homeomorph e)
  · intro z hz
    have hf := hd.differentiableAt (isOpen_ball.mem_nhds (cayley_mem_ball hz))
    have hc := differentiableOn_cayley.differentiableAt (isOpen_upper.mem_nhds hz)
    have h := hf.hasDerivAt.comp z hc.hasDerivAt
    rw [h.deriv]
    exact mul_ne_zero (hderiv (cayley z) (cayley_mem_ball hz)) (deriv_cayley_ne_zero hz)
  · intro w hw
    obtain ⟨v, hv, hvw⟩ := hsurj hw
    refine ⟨⟨cayleyInv v, im_cayleyInv_pos hv⟩, ?_⟩
    change f (cayley (cayleyInv v)) = w
    rwa [cayley_cayleyInv hv]

end LatticeComplementCover

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
