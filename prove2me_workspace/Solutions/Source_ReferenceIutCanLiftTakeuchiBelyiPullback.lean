/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/S1/Belyi.lean, lines 23–69 and 80–100
-/
import Solutions.Source_ReferenceIutCanLiftLatticeParameterization
import Solutions.Source_ReferenceIutCanLiftTakeuchiEllipticOrbifoldCover
import Solutions.Source_ReferenceIutCanLiftTakeuchiRationalPoles
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi

open AbcAdaptation.Reference.Heights
open Polynomial Set WeierstrassCurve
open scoped UpperHalfPlane

/-- In a short model, the finite two-torsion coordinates are the points on the line `y = 0`. -/
theorem mem_twoTorsionX_iff (τ : ℍ) (C : VariableChange ℂ)
    (h1 : (C • latticeCurve τ).a₁ = 0)
    (h3 : (C • latticeCurve τ).a₃ = 0) (x : ℂ) :
    x ∈ twoTorsionX τ ((C.u : ℂ)⁻¹ ^ 2) (-(C.u : ℂ)⁻¹ ^ 2 * C.r) ↔
      (C • latticeCurve τ).toAffine.Equation x 0 := by
  let L := periodPair τ
  have hu : (C.u : ℂ) ≠ 0 := C.u.ne_zero
  have hi : (C.u : ℂ)⁻¹ ≠ 0 := inv_ne_zero hu
  have hs : C.s = 0 := by
    have h : (C.u : ℂ)⁻¹ * (2 * C.s) = 0 := by
      simpa only [variableChange_a₁, latticeCurve, zero_add, Units.val_inv_eq_inv_val] using h1
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hi)).resolve_left two_ne_zero
  have ht : C.t = 0 := by
    have h : (C.u : ℂ)⁻¹ ^ 3 * (2 * C.t) = 0 := by
      simpa only [variableChange_a₃, latticeCurve, mul_zero, add_zero, zero_add,
        Units.val_inv_eq_inv_val] using h3
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left
      (pow_ne_zero _ hi))).resolve_left two_ne_zero
  have hcoord (v : ℂ) :
      (latticeParameterization τ C v).1 =
        (C.u : ℂ)⁻¹ ^ 2 * L.weierstrassP v + -(C.u : ℂ)⁻¹ ^ 2 * C.r := by
    change vcX C (L.weierstrassP v) = _
    rw [vcX, div_eq_mul_inv, inv_pow]
    ring
  have hcoordY (v : ℂ) :
      (latticeParameterization τ C v).2 =
        L.derivWeierstrassP v / 2 / (C.u : ℂ) ^ 3 := by
    simp only [latticeParameterization, vcY, ht, hs, sub_zero, zero_mul, L]
  constructor
  · rintro ⟨v, ⟨hv2, hv⟩, rfl⟩
    have hv' : v = -v + 2 • v := by rw [two_nsmul]; ring
    have h := L.derivWeierstrassP_add_coe (-v) ⟨2 • v, hv2⟩
    change L.derivWeierstrassP (-v + 2 • v) = L.derivWeierstrassP (-v) at h
    rw [← hv', L.derivWeierstrassP_neg] at h
    have hd : L.derivWeierstrassP v = 0 := by linear_combination h / 2
    have he := latticeParameterization_equation τ C hv
    rw [hcoord, hcoordY, hd, zero_div, zero_div] at he
    exact he
  · intro hx
    obtain ⟨v, hv, hp⟩ := latticeParameterization_surjective τ C hx
    have hy := congrArg Prod.snd hp
    change (latticeParameterization τ C v).2 = 0 at hy
    rw [hcoordY] at hy
    have hd : L.derivWeierstrassP v = 0 :=
      (div_eq_zero_iff.mp ((div_eq_zero_iff.mp hy).resolve_right
        (pow_ne_zero _ hu))).resolve_right two_ne_zero
    refine ⟨v, ⟨?_, hv⟩, ?_⟩
    · rw [two_nsmul]
      exact add_self_mem_of_derivWeierstrassP_eq_zero L hv hd
    · exact (hcoord v).symm.trans (congrArg Prod.fst hp)

/-- Pull the certified rational function back to the complement of the period lattice. -/
theorem RatCert.ellipticOrbifoldCover {f N D H K R : ℂ[X]} {c : ℂ}
    (hc : RatCert f N D H K R c) (τ : ℍ) (C : VariableChange ℂ)
    (h1 : (C • latticeCurve τ).a₁ = 0) (h3 : (C • latticeCurve τ).a₃ = 0)
    (hf : ∀ x, f.eval x = x ^ 3 + (C • latticeCurve τ).a₂ * x ^ 2 +
      (C • latticeCurve τ).a₄ * x + (C • latticeCurve τ).a₆) :
    let a : ℂ := (C.u : ℂ)⁻¹ ^ 2
    let r : ℂ := -a * C.r
    let F := fun z ↦ hc.G (ellX τ a r z)
    IsOrbCover F ((periodPair τ).lattice : Set ℂ)ᶜ sig ∧
      (∀ z ∉ (periodPair τ).lattice, HasLocalForm F z (sig (F z))) ∧
      (∀ z, ∀ l ∈ (periodPair τ).lattice, F (z + 2 * l) = F z) := by
  let a : ℂ := (C.u : ℂ)⁻¹ ^ 2
  let r : ℂ := -a * C.r
  have ha : a ≠ 0 := pow_ne_zero _ (inv_ne_zero C.u.ne_zero)
  have hZ : twoTorsionX τ a r = {x | f.eval x = 0} := by
    ext x
    rw [mem_twoTorsionX_iff τ C h1 h3, Affine.equation_iff, mem_ofPred_eq, hf]
    simp only [mul_zero, add_zero, zero_pow two_ne_zero]
    exact eq_comm
  obtain ⟨hCover, hLocal⟩ := ellOrbStatement τ a r hc.G ha
    (by rw [hZ]; exact hc.differentiableOn)
    (by rw [hZ]; exact fun _ hx ↦ hc.hasLocalForm hx)
    (by rw [hZ]; exact hc.finite_fiber)
    (by rw [hZ]; exact hc.surj)
    (by rw [hZ]; exact fun _ hz ↦ hc.tendsto_nhdsNE hz) hc.tendsto_cobounded
  refine ⟨hCover, hLocal, fun z l hl ↦ ?_⟩
  change hc.G (ellX τ a r (z + 2 * l)) = hc.G (ellX τ a r z)
  simp only [ellX]
  rw [show (z + 2 * l) / 2 = z / 2 + l by ring,
    (periodPair τ).weierstrassP_add_coe (z / 2) ⟨l, hl⟩]

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi
