/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/S1/Mobius.lean
-/
import Solutions.Source_ReferenceIutCanLiftHalfPlaneAut
import Solutions.Source_ReferenceHeightsModularJFibers
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.LocallyCompactRegular

set_option autoImplicit false

open Complex Filter Function Set Topology
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi

private theorem holomorphicH_id : HolomorphicH id := by
  exact differentiableOn_id.congr fun z hz ↦ ofComplex_of_im_pos hz

theorem holomorphicH_comp {T S : ℍ → ℍ} (hT : HolomorphicH T) (hS : HolomorphicH S) :
    HolomorphicH (T ∘ S) := by
  unfold HolomorphicH at *
  refine (hT.comp hS fun z _ ↦ (S (ofComplex z)).im_pos).congr fun z _ ↦ ?_
  simp only [Function.comp_apply, ofComplex_apply]

theorem holomorphicH_smul (g : SL(2, ℝ)) : HolomorphicH fun τ ↦ g • τ :=
  holomorphicH_id.smul g

private theorem continuous_of_holomorphicH {H : ℍ → ℍ} (hH : HolomorphicH H) :
    Continuous H := by
  have hc : Continuous fun τ : ℍ ↦ (H τ : ℂ) := by
    refine (hH.continuousOn.comp_continuous continuous_coe fun τ ↦ τ.im_pos).congr fun τ ↦ ?_
    simp only [Function.comp_apply, ofComplex_apply]
  exact isEmbedding_coe.continuous_iff.mpr hc

private theorem eq_of_eqOn_open {T S : ℍ → ℍ} (hT : HolomorphicH T) (hS : HolomorphicH S)
    {V : Set ℍ} (hV : IsOpen V) (hne : V.Nonempty) (heq : EqOn T S V) : T = S := by
  obtain ⟨τ₀, hτ₀⟩ := hne
  let t : ℂ → ℂ := fun z ↦ (T (ofComplex z) : ℂ)
  let s : ℂ → ℂ := fun z ↦ (S (ofComplex z) : ℂ)
  have ht : AnalyticOnNhd ℂ t {z | 0 < z.im} := hT.analyticOnNhd isOpen_upper
  have hs : AnalyticOnNhd ℂ s {z | 0 < z.im} := hS.analyticOnNhd isOpen_upper
  have hV' : IsOpen (((↑) : ℍ → ℂ) '' V) := isOpenEmbedding_coe.isOpenMap _ hV
  have hev : t =ᶠ[𝓝 (τ₀ : ℂ)] s := by
    filter_upwards [hV'.mem_nhds ⟨τ₀, hτ₀, rfl⟩] with z hz
    obtain ⟨σ, hσ, rfl⟩ := hz
    simp only [t, s, ofComplex_apply, heq hσ]
  have h := ht.eqOn_of_preconnected_of_eventuallyEq hs
    (convex_halfSpace_im_gt 0).isPreconnected τ₀.im_pos hev
  funext τ
  apply UpperHalfPlane.ext
  simpa only [t, s, ofComplex_apply] using h τ.im_pos

/-- A holomorphic self-map of the upper half-plane with a holomorphic left inverse is Möbius. -/
theorem exists_SL2R_eq_of_leftInverse {T S : ℍ → ℍ} (hT : HolomorphicH T) (hS : HolomorphicH S)
    (hST : ∀ τ, S (T τ) = τ) : ∃ g : SL(2, ℝ), ∀ τ, T τ = g • τ := by
  let t : ℂ → ℂ := fun z ↦ (T (ofComplex z) : ℂ)
  let H : Set ℂ := {z | 0 < z.im}
  have ht : AnalyticOnNhd ℂ t H := hT.analyticOnNhd isOpen_upper
  have hOpen := (ht.is_constant_or_isOpen (convex_halfSpace_im_gt 0).isPreconnected).resolve_left
    (by
      rintro ⟨c, hc⟩
      let w : ℍ := ⟨1 + I, by simp⟩
      have hw (τ : ℍ) : (T τ : ℂ) = c := by
        simpa only [t, ofComplex_apply] using hc τ τ.im_pos
      have hEq : UpperHalfPlane.I = w :=
        (show LeftInverse S T from hST).injective <|
          UpperHalfPlane.ext ((hw UpperHalfPlane.I).trans (hw w).symm)
      have hre := congrArg (fun τ : ℍ ↦ (τ : ℂ).re) hEq
      simp [w, UpperHalfPlane.coe_I] at hre)
  have hRange : IsOpen (range T) := by
    have hEq : range T = ((↑) : ℍ → ℂ) ⁻¹' (t '' H) := by
      ext τ
      constructor
      · rintro ⟨σ, rfl⟩
        exact ⟨σ, σ.im_pos, by simp only [t, ofComplex_apply]⟩
      · rintro ⟨z, _, h⟩
        exact ⟨ofComplex z, UpperHalfPlane.ext h⟩
    rw [hEq]
    exact (hOpen H subset_rfl isOpen_upper).preimage continuous_coe
  have hTS : T ∘ S = id := eq_of_eqOn_open (holomorphicH_comp hT hS) holomorphicH_id
    hRange (range_nonempty T) (by
      rintro _ ⟨τ, rfl⟩
      change T (S (T τ)) = T τ
      rw [hST])
  exact exists_SL2R_eq_of_holomorphic hT hS (congrFun hTS) hST

/-- The image of an integral modular matrix in the real special linear group. -/
abbrev toSLR (δ : SL(2, ℤ)) : SL(2, ℝ) := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) δ

private theorem toSLR_smul (δ : SL(2, ℤ)) (τ : ℍ) : toSLR δ • τ = δ • τ := by
  ext
  rw [coe_specialLinearGroup_apply, coe_specialLinearGroup_apply] <;> simp

/-- A holomorphic self-map preserving the modular invariant acts as an integral modular matrix. -/
theorem exists_SL2Z_eq_of_modularJ {H : ℍ → ℍ} (hH : HolomorphicH H)
    (hj : ∀ τ, AbcAdaptation.Reference.Heights.modularJ (H τ) =
      AbcAdaptation.Reference.Heights.modularJ τ) : ∃ δ : SL(2, ℤ), ∀ τ, H τ = toSLR δ • τ := by
  letI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  letI : Countable SL(2, ℤ) := Function.Injective.countable
    (f := fun A : SL(2, ℤ) ↦ (A : Matrix (Fin 2) (Fin 2) ℤ)) Subtype.coe_injective
  let S : SL(2, ℤ) → Set ℍ := fun δ ↦ {τ | H τ = toSLR δ • τ}
  have hHc := continuous_of_holomorphicH hH
  have hS : ∀ δ, IsClosed (S δ) := fun δ ↦
    isClosed_eq hHc (continuous_of_holomorphicH (holomorphicH_smul (toSLR δ)))
  have hU : ⋃ δ, S δ = univ := by
    refine eq_univ_of_forall fun τ ↦ mem_iUnion.mpr ?_
    obtain ⟨δ, hδ⟩ := AbcAdaptation.Reference.Heights.exists_smul_eq_of_modularJ_eq (H τ) τ (hj τ)
    exact ⟨δ, by simpa only [S, mem_ofPred_eq, toSLR_smul] using hδ.symm⟩
  obtain ⟨δ, hδ⟩ := nonempty_interior_of_iUnion_of_closed hS hU
  refine ⟨δ, congrFun ?_⟩
  exact eq_of_eqOn_open hH (holomorphicH_smul (toSLR δ)) isOpen_interior hδ
    fun σ hσ ↦ (interior_subset hσ : σ ∈ S δ)

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi
