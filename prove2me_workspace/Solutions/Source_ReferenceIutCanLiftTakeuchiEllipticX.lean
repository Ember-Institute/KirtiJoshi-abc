/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original paths OrbicurveCores/S1/Defs.lean, lines 80–89, and
OrbicurveCores/S1/EllOrb.lean, lines 104–192.
-/
import Solutions.Source_ReferenceHeightsWeierstrassPFiber
import Solutions.Source_ReferenceHeightsWeierstrassSurjectivity
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi

open AbcAdaptation.Reference.Heights Set

local notation "𝓛" => periodPair

/-- The `x`-coordinate `a ℘(u / 2) + r` of `C` along `ℂ / Λ`, halved: its critical points and poles
are exactly the lattice `Λ`, so `u ↦ G (ellX τ a r u)` is unramified over the `x`-line off `Λ`. -/
noncomputable def ellX (τ : UpperHalfPlane) (a r : ℂ) (u : ℂ) : ℂ :=
  a * (periodPair τ).weierstrassP (u / 2) + r

/-- The `x`-coordinates `a ℘(v) + r` of the nonzero `2`-torsion points of `ℂ / Λ`. -/
def twoTorsionX (τ : UpperHalfPlane) (a r : ℂ) : Set ℂ :=
  (fun v ↦ a * (periodPair τ).weierstrassP v + r) ''
    {v | 2 • v ∈ (periodPair τ).lattice ∧
      v ∉ (periodPair τ).lattice}

theorem half_notMem (L : PeriodPair) {u : ℂ} (hu : u ∉ L.lattice) : u / 2 ∉ L.lattice :=
  fun h ↦ hu (by simpa only [add_halves] using L.lattice.add_mem h h)

theorem add_self_mem_of_derivWeierstrassP_eq_zero (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice)
    (h : L.derivWeierstrassP z = 0) : z + z ∈ L.lattice := by
  have hz' : -z ∉ L.lattice := by rwa [neg_mem_iff]
  have := (weierstrassP_deriv_eq_iff_sub_mem L z (-z) hz hz').mp
    ⟨(L.weierstrassP_neg z).symm, by rw [L.derivWeierstrassP_neg, h, neg_zero]⟩
  rwa [sub_neg_eq_add] at this

/-- The sign `±1` attached to a boolean. -/
def sgn : Bool → ℂ
  | true => 1
  | false => -1

theorem sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> norm_num [sgn]

theorem sgn_mul_mem {L : PeriodPair} (b : Bool) {z : ℂ} (hz : z ∈ L.lattice) :
    sgn b * z ∈ L.lattice := by
  cases b
  · rw [sgn, neg_one_mul]; exact neg_mem hz
  · rw [sgn, one_mul]; exact hz

variable {τ : UpperHalfPlane} {a r : ℂ}

theorem analyticAt_ellX {u : ℂ} (hu : u ∉ (𝓛 τ).lattice) : AnalyticAt ℂ (ellX τ a r) u := by
  have h := (𝓛 τ).analyticOnNhd_weierstrassP (u / 2) (half_notMem _ hu)
  have h2 : AnalyticAt ℂ (fun u : ℂ ↦ u / 2) u := analyticAt_id.div_const
  exact (analyticAt_const.mul
    (AnalyticAt.comp (g := (𝓛 τ).weierstrassP) (f := fun u : ℂ ↦ u / 2) h h2)).add analyticAt_const

theorem hasDerivAt_ellX {u : ℂ} (hu : u ∉ (𝓛 τ).lattice) :
    HasDerivAt (ellX τ a r) (a * ((𝓛 τ).derivWeierstrassP (u / 2) * (1 / 2))) u := by
  have h : HasDerivAt (𝓛 τ).weierstrassP ((𝓛 τ).derivWeierstrassP (u / 2)) (u / 2) := by
    rw [← PeriodPair.deriv_weierstrassP]
    exact ((𝓛 τ).analyticOnNhd_weierstrassP _ (half_notMem _ hu)).differentiableAt.hasDerivAt
  have h2 : HasDerivAt (fun u : ℂ ↦ u / 2) (1 / 2) u := (hasDerivAt_id' u).div_const 2
  exact ((h.comp u h2).const_mul a).add_const r

theorem deriv_ellX_ne_zero (ha : a ≠ 0) {u : ℂ} (hu : u ∉ (𝓛 τ).lattice) :
    deriv (ellX τ a r) u ≠ 0 := by
  rw [(hasDerivAt_ellX hu).deriv]
  refine mul_ne_zero ha (mul_ne_zero (fun h0 ↦ hu ?_) (by norm_num))
  have := add_self_mem_of_derivWeierstrassP_eq_zero _ (half_notMem _ hu) h0
  rwa [add_halves] at this

theorem ellX_notMem_twoTorsionX (ha : a ≠ 0) {u : ℂ} (hu : u ∉ (𝓛 τ).lattice) :
    ellX τ a r u ∉ twoTorsionX τ a r := by
  rintro ⟨v, ⟨hv2, hv⟩, hq⟩
  simp only [ellX, add_left_inj] at hq
  have hp := mul_left_cancel₀ ha hq
  have hv2' : v + v ∈ (𝓛 τ).lattice := by rwa [two_nsmul] at hv2
  rcases (weierstrassP_eq_iff_sub_mem_or_add_mem _ v (u / 2) hv
    (half_notMem _ hu)).mp hp with h | h
  · apply hu
    have := sub_mem (sub_mem hv2' h) h
    convert this using 1; ring
  · apply hu
    have := sub_mem (add_mem h h) hv2'
    convert this using 1; ring

theorem exists_ellX_eq (ha : a ≠ 0) {x : ℂ} (hx : x ∉ twoTorsionX τ a r) :
    ∃ u ∉ (𝓛 τ).lattice, ellX τ a r u = x := by
  obtain ⟨v, hv, hpv⟩ := exists_notMem_lattice_weierstrassP_eq (𝓛 τ) ((x - r) / a)
  have hq : a * (𝓛 τ).weierstrassP v + r = x := by
    rw [hpv, mul_div_cancel₀ _ ha, sub_add_cancel]
  refine ⟨2 * v, fun h ↦ hx ⟨v, ⟨by rwa [two_nsmul, ← two_mul], hv⟩, hq⟩, ?_⟩
  simp only [ellX, mul_div_cancel_left₀ v two_ne_zero]
  exact hq

theorem ellX_eq_or (ha : a ≠ 0) {u u' : ℂ} (hu : u ∉ (𝓛 τ).lattice) (hu' : u' ∉ (𝓛 τ).lattice)
    (h : ellX τ a r u' = ellX τ a r u) :
    ∃ μ ∈ (𝓛 τ).lattice, u' = u + 2 * μ ∨ u' = -u + 2 * μ := by
  simp only [ellX, add_left_inj] at h
  rcases (weierstrassP_eq_iff_sub_mem_or_add_mem _ (u' / 2) (u / 2) (half_notMem _ hu')
    (half_notMem _ hu)).mp (mul_left_cancel₀ ha h) with h' | h'
  · exact ⟨_, h', Or.inl (by ring)⟩
  · exact ⟨_, h', Or.inr (by ring)⟩

theorem ellX_sgn (b : Bool) {μ : ℂ} (hμ : μ ∈ (𝓛 τ).lattice) (y : ℂ) :
    ellX τ a r (sgn b * (y - 2 * μ)) = ellX τ a r y := by
  simp only [ellX]
  have e : sgn b * (y - 2 * μ) / 2 = sgn b * (y / 2 - μ) := by ring
  have hsub := (𝓛 τ).weierstrassP_sub_coe (y / 2) ⟨μ, hμ⟩
  rw [e]
  cases b
  · rw [sgn, neg_one_mul, PeriodPair.weierstrassP_neg, hsub]
  · rw [sgn, one_mul, hsub]

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi
