/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original paths OrbicurveCores/S1/Rigidity/Transfer.lean, lines 220–277,
and OrbicurveCores/S1/Rigidity.lean
-/
import Solutions.Source_ReferenceIutCanLiftTakeuchiRigidityTransfer
import Solutions.Source_ReferenceIutCanLiftTakeuchiModelRigidity
import Solutions.Source_ReferenceHeightsPeriodPairScaling
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Filter Function Set Topology
open UpperHalfPlane hiding I

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi

open AbcAdaptation.Reference.Heights WeierstrassCurve

namespace Rigidity

variable {τ τ' : ℍ} {σ σ' : ℂ → ℂ}

/-- The map of lattice quotients lifts to multiplication by a complex number. -/
private theorem exists_linear (hσ : IsLatticeLift τ σ) (hσ' : IsLatticeLift τ' σ')
    (hrel : SameFibres τ τ' σ σ') :
    ∃ a : ℂ, ∀ x, quotientMk τ' (a * x) = transfer τ τ' σ σ' (quotientMk τ x) := by
  obtain ⟨β, hβd, hβ0, hβ'⟩ := exists_entire_lift hσ hσ' hrel
  have hβc' := hβd.continuous
  -- Translating by a period changes β by a constant period.
  have hper : ∀ l ∈ (periodPair τ).lattice, ∀ x, β (x + l) = β x + (β l - β 0) := by
    intro l hl x
    have hFm : MapsTo (fun y ↦ β (y + l) - β y) univ (periodPair τ').lattice := by
      intro y _
      change β (y + l) - β y ∈ (periodPair τ').lattice
      rw [← quotientMk_eq_iff τ', hβ', hβ',
        (quotientMk_eq_iff τ).mpr (by rwa [add_sub_cancel_left])]
    have : β (x + l) - β x = β (0 + l) - β 0 :=
      isPreconnected_univ.constant_of_mapsTo (isDiscrete_lattice τ')
        ((hβc'.comp (continuous_id.add continuous_const)).sub hβc').continuousOn hFm
        (mem_univ x) (mem_univ 0)
    rw [zero_add] at this
    rw [← this]
    ring
  have hderiv_per : ∀ z w, w ∈ (periodPair τ).lattice → deriv β (z + w) = deriv β z := by
    intro z w hw
    have h1 : (fun y ↦ β (y + w)) = fun y ↦ β y + (β w - β 0) := funext (hper w hw)
    have h2 := congrArg (fun f ↦ deriv f z) h1
    simpa only [deriv_comp_add_const, deriv_add_const] using h2
  -- The periodic derivative is bounded, so Liouville gives a constant derivative.
  have hdd : Differentiable ℂ (deriv β) :=
    differentiableOn_univ.mp (hβd.differentiableOn.deriv isOpen_univ)
  have hbdd := IsZLattice.isCompact_range_of_periodic (periodPair τ).lattice (deriv β) hdd.continuous
    hderiv_per
  have hconst : ∀ x, deriv β x = deriv β 0 := fun x ↦
    hdd.apply_eq_apply_of_bounded hbdd.isBounded x 0
  refine ⟨deriv β 0, fun x ↦ ?_⟩
  have hG : Differentiable ℂ (fun y ↦ β y - deriv β 0 * y) :=
    hβd.sub (differentiable_id.const_mul _)
  have hG' : ∀ y, deriv (fun y ↦ β y - deriv β 0 * y) y = 0 := by
    intro y
    have hD : HasDerivAt (fun y ↦ β y - deriv β 0 * y) (deriv β y - deriv β 0 * 1) y :=
      (hβd y).hasDerivAt.sub ((hasDerivAt_id y).const_mul (deriv β 0))
    rw [hD.deriv, hconst y, mul_one, sub_self]
  have := is_const_of_deriv_eq_zero hG hG' x 0
  simp only [mul_zero, sub_zero, hβ0] at this
  rw [← hβ', show β x = deriv β 0 * x by linear_combination this]

/-- **Two lifts with the same fibres give homothetic lattices.** -/
theorem exists_homothety (hσ : IsLatticeLift τ σ) (hσ' : IsLatticeLift τ' σ')
    (hrel : SameFibres τ τ' σ σ') :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ x, x ∈ (periodPair τ).lattice ↔ a * x ∈ (periodPair τ').lattice := by
  obtain ⟨a, ha⟩ := exists_linear hσ hσ' hrel
  obtain ⟨a', ha'⟩ := exists_linear hσ' hσ hrel.symm
  have hcomp : ∀ x, quotientMk τ (a' * (a * x)) = quotientMk τ x := fun x ↦ by
    rw [ha', ha, transfer_transfer hσ hσ' hrel]
  have hFm : MapsTo (fun x : ℂ ↦ (a' * a - 1) * x) univ (periodPair τ).lattice := by
    intro x _
    change (a' * a - 1) * x ∈ (periodPair τ).lattice
    rw [show (a' * a - 1) * x = a' * (a * x) - x by ring]
    exact (quotientMk_eq_iff τ).mp (hcomp x)
  have h1 : (a' * a - 1) * 1 = (a' * a - 1) * 0 :=
    isPreconnected_univ.constant_of_mapsTo (isDiscrete_lattice τ)
      (continuous_const.mul continuous_id).continuousOn hFm (mem_univ 1) (mem_univ 0)
  rw [mul_one, mul_zero, sub_eq_zero] at h1
  refine ⟨a, fun h ↦ by simp [h] at h1, fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩⟩
  · rw [← quotientMk_eq_zero_iff τ', ha, transfer_mk_of_mem hσ hx]
  · rw [← quotientMk_eq_zero_iff τ, ← hcomp, ha', transfer_mk_of_mem hσ' hx]

private theorem mem_periodPairScale_lattice {a : ℂ} (ha : a ≠ 0) (L : PeriodPair) {y : ℂ} :
    y ∈ (periodPairScale a ha L).lattice ↔ a⁻¹ * y ∈ L.lattice := by
  constructor
  · intro hy
    exact ((periodPairScaleLatticeEquiv a ha L).symm ⟨y, hy⟩).2
  · intro hy
    have := ((periodPairScaleLatticeEquiv a ha L) ⟨a⁻¹ * y, hy⟩).2
    rwa [periodPairScaleLatticeEquiv_coe, ← mul_assoc, mul_inv_cancel₀ ha, one_mul] at this

private theorem G_eq_of_lattice_eq {L M : PeriodPair} (h : L.lattice = M.lattice) (n : ℕ) :
    L.G n = M.G n := by
  unfold PeriodPair.G
  rw [h]

private theorem modularJ_eq_formula (t : ℍ) :
    modularJ t = ((periodPair t).g₂ ^ 3 - 27 * (periodPair t).g₃ ^ 2)⁻¹ *
      (12 * (periodPair t).g₂) ^ 3 := by
  letI : (latticeCurve t).IsElliptic := latticeCurve_isElliptic t
  have hc₄ : (latticeCurve t).c₄ = 12 * (periodPair t).g₂ := by
    simp [latticeCurve, c₄, b₂, b₄]
    ring
  rw [← latticeCurve_j_eq_modularJ t, j, Units.val_inv_eq_inv_val, coe_Δ',
    latticeCurve_discriminant, hc₄]

/-- Homothetic period lattices have the same `j`-invariant. -/
theorem modularJ_eq_of_homothety {a : ℂ} (ha : a ≠ 0)
    (h : ∀ x, x ∈ (periodPair τ).lattice ↔ a * x ∈ (periodPair τ').lattice) :
    modularJ τ = modularJ τ' := by
  have hlat : (periodPairScale a ha (periodPair τ)).lattice = (periodPair τ').lattice := by
    ext y
    rw [mem_periodPairScale_lattice, h, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  have hg₂ : (periodPair τ').g₂ = a⁻¹ ^ 4 * (periodPair τ).g₂ := by
    rw [← periodPairScale_g₂ a ha, PeriodPair.g₂, PeriodPair.g₂, G_eq_of_lattice_eq hlat]
  have hg₃ : (periodPair τ').g₃ = a⁻¹ ^ 6 * (periodPair τ).g₃ := by
    rw [← periodPairScale_g₃ a ha, PeriodPair.g₃, PeriodPair.g₃, G_eq_of_lattice_eq hlat]
  letI : (latticeCurve τ).IsElliptic := latticeCurve_isElliptic τ
  have hΔ := (latticeCurve τ).isUnit_Δ.ne_zero
  rw [latticeCurve_discriminant] at hΔ
  rw [modularJ_eq_formula τ, modularJ_eq_formula τ', hg₂, hg₃,
    show (a⁻¹ ^ 4 * (periodPair τ).g₂) ^ 3 - 27 * (a⁻¹ ^ 6 * (periodPair τ).g₃) ^ 2 =
      a⁻¹ ^ 12 * ((periodPair τ).g₂ ^ 3 - 27 * (periodPair τ).g₃ ^ 2) by ring]
  field_simp [ha, hΔ] <;> ring

end Rigidity

open scoped MatrixGroups in
/-- Two punctured elliptic curves uniformized by the same pair have the same `j`-invariant. -/
theorem j_eq_of_uniformizes (W W' : WeierstrassCurve ℂ) [W.IsElliptic] [W'.IsElliptic]
    {pair : SL(2, ℝ) × SL(2, ℝ)} (hW : Uniformizes W pair) (hW' : Uniformizes W' pair) :
    W.j = W'.j := by
  obtain ⟨π, hπ⟩ := hW
  obtain ⟨π', hπ'⟩ := hW'
  obtain ⟨τ, hj, σ, hσ, hFibre⟩ := Rigidity.exists_isLatticeLift hπ
  obtain ⟨τ', hj', σ', hσ', hFibre'⟩ := Rigidity.exists_isLatticeLift hπ'
  have hRel : Rigidity.SameFibres τ τ' σ σ' := fun z w hz hw ↦
    (hFibre ⟨z, hz⟩ ⟨w, hw⟩).trans (hFibre' ⟨z, hz⟩ ⟨w, hw⟩).symm
  obtain ⟨a, ha, hlat⟩ := Rigidity.exists_homothety hσ hσ' hRel
  rw [hj, hj', Rigidity.modularJ_eq_of_homothety ha hlat]

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi
