/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original paths OrbicurveCores/S1/Defs.lean, lines 91–106, and
OrbicurveCores/S1/EllOrb.lean, lines 194–352.
-/
import Solutions.Source_ReferenceIutCanLiftTakeuchiOrbifoldCover
import Solutions.Source_ReferenceIutCanLiftTakeuchiEllipticX
import Solutions.Source_ReferenceIutCanLiftHolomorphicInverse
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi

open AbcAdaptation.Reference.Heights
open Bornology Filter Function Metric Set
open scoped Topology

local notation "𝓛" => periodPair

/-- **Pulling back an orbifold covering of the `x`-line.** If `G` is holomorphic off the
`2`-torsion `x`-coordinates `Z`, has poles at `Z` and at `∞`, finite fibres, attains every value,
and has local normal forms of order `sig (G x)`, then `F = G ∘ ellX` is an orbifold covering on
`ℂ ∖ Λ` with local normal forms of order `sig (F u)`. -/
def EllOrbStatement : Prop :=
  ∀ (τ : UpperHalfPlane) (a r : ℂ) (G : ℂ → ℂ), a ≠ 0 →
    DifferentiableOn ℂ G (twoTorsionX τ a r)ᶜ →
    (∀ x ∉ twoTorsionX τ a r, HasLocalForm G x (sig (G x))) →
    (∀ w, {x | x ∉ twoTorsionX τ a r ∧ G x = w}.Finite) →
    (∀ w, ∃ x ∉ twoTorsionX τ a r, G x = w) →
    (∀ z ∈ twoTorsionX τ a r, Tendsto G (𝓝[≠] z) (Bornology.cobounded ℂ)) →
    Tendsto G (Bornology.cobounded ℂ) (Bornology.cobounded ℂ) →
    IsOrbCover (fun u ↦ G (ellX τ a r u))
        ((periodPair τ).lattice : Set ℂ)ᶜ sig ∧
      ∀ u ∉ (periodPair τ).lattice,
        HasLocalForm (fun u ↦ G (ellX τ a r u)) u (sig (G (ellX τ a r u)))

variable {τ : UpperHalfPlane} {a r : ℂ}

/-- Chart data of `G ∘ ellX` at a point `u₀` over a solution `x ∉ Z` of `G x = w`: an open `E`
around `u₀` on which `g ∘ ellX` is a biholomorphism onto `ball 0 ρ₀` with inverse `ψ`, and an open
neighbourhood `M` of `x` covered by `ellX '' E` on which `G = w + g ^ n`. -/
private theorem exists_pointData {G : ℂ → ℂ} {w x : ℂ} {n : ℕ} {B : Set ℂ} (ha : a ≠ 0)
    (hx : x ∉ twoTorsionX τ a r) (hGx : G x = w) (hloc : HasLocalForm G x n)
    (hB : IsOpen B) (hxB : x ∈ B) :
    ∃ ρ₀ > (0 : ℝ), ∃ (g ψ : ℂ → ℂ) (E M : Set ℂ),
      IsOpen E ∧ E ⊆ ((𝓛 τ).lattice : Set ℂ)ᶜ ∧
      ContinuousOn (fun y ↦ g (ellX τ a r y)) E ∧
      (∀ y ∈ E, ellX τ a r y ∈ B ∧ G (ellX τ a r y) = w + g (ellX τ a r y) ^ n) ∧
      MapsTo ψ (ball 0 ρ₀) E ∧ (∀ y ∈ E, ψ (g (ellX τ a r y)) = y) ∧
      (∀ t ∈ ball (0 : ℂ) ρ₀, g (ellX τ a r (ψ t)) = t) ∧ DifferentiableOn ℂ ψ (ball 0 ρ₀) ∧
      IsOpen M ∧ x ∈ M ∧ ∀ x' ∈ M, G x' = w + g x' ^ n ∧ ∃ y ∈ E, ellX τ a r y = x' := by
  obtain ⟨u₀, hu₀, hqu₀⟩ := exists_ellX_eq (r := r) ha hx
  obtain ⟨g, hg, hg0, hgd, hev⟩ := hloc
  rw [hGx] at hev
  obtain ⟨N, hNev, hNo, hxN⟩ := _root_.eventually_nhds_iff.mp hev
  have hq : AnalyticAt ℂ (ellX τ a r) u₀ := analyticAt_ellX hu₀
  have hqd0 : deriv (ellX τ a r) u₀ ≠ 0 := deriv_ellX_ne_zero ha hu₀
  set φ := fun y ↦ g ((ellX τ a r) y)
  have hgq : AnalyticAt ℂ g ((ellX τ a r) u₀) := by rw [hqu₀]; exact hg
  have hφ : AnalyticAt ℂ φ u₀ := hgq.comp hq
  have hφd : deriv φ u₀ ≠ 0 := by
    rw [show φ = g ∘ (ellX τ a r) from rfl,
      deriv_comp _ hgq.differentiableAt hq.differentiableAt, hqu₀]
    exact mul_ne_zero hgd hqd0
  have h4 : ∀ᶠ y in 𝓝 u₀, (ellX τ a r) y ∈ B ∩ N := by
    refine hq.continuousAt.tendsto.eventually ?_
    rw [hqu₀]
    exact (hB.inter hNo).mem_nhds ⟨hxB, hxN⟩
  have hev2 : ∀ᶠ y in 𝓝 u₀,
      y ∉ (𝓛 τ).lattice ∧ AnalyticAt ℂ φ y ∧ deriv φ y ≠ 0 ∧ (ellX τ a r) y ∈ B ∩ N :=
    Filter.Eventually.and ((𝓛 τ).isClosed_lattice.isOpen_compl.mem_nhds hu₀)
      (hφ.eventually_analyticAt.and ((hφ.deriv.continuousAt.eventually_ne hφd).and h4))
  obtain ⟨O, hOP, hOo, hu₀O⟩ := _root_.eventually_nhds_iff.mp hev2
  obtain ⟨ρ₀, hρ₀, E, ψ, hEo, hEO, hu₀E, hψ, hψφ, hφψ, hψd⟩ :=
    exists_chart hOo hu₀O (fun y hy ↦ (hOP y hy).2.1) (fun y hy ↦ (hOP y hy).2.2.1)
      (by simp only [φ, hqu₀, hg0])
  obtain ⟨ε, hε, s, hsc, hsq, hs0⟩ := HolomorphicInverse.exists_localSection hq.hasStrictDerivAt hqd0
  rw [hqu₀] at hsc hsq hs0
  refine ⟨ρ₀, hρ₀, g, ψ, E, ball x ε ∩ s ⁻¹' E ∩ N, hEo, fun y hy ↦ (hOP y (hEO hy)).1,
    fun y hy ↦ (hOP y (hEO hy)).2.1.continuousAt.continuousWithinAt, fun y hy ↦ ?_, hψ, hψφ,
    hφψ, hψd, (hsc.isOpen_inter_preimage isOpen_ball hEo).inter hNo,
    ⟨⟨mem_ball_self hε, by rw [mem_preimage, hs0]; exact hu₀E⟩, hxN⟩,
    fun x' hx' ↦ ⟨hNev x' hx'.2, s x', hx'.1.2, hsq x' hx'.1.1⟩⟩
  have hy' := (hOP y (hEO hy)).2.2.2
  exact ⟨hy'.1, hNev _ hy'.2⟩

/-! ### The main theorem -/

theorem ellOrbStatement : EllOrbStatement := by
  intro τ a r G ha hdiff hloc hfin hsurj hpole hinf
  set Z := twoTorsionX τ a r
  refine ⟨fun w ↦ ⟨?_, ?_⟩, fun u hu ↦ ?_⟩
  · obtain ⟨x, hx, rfl⟩ := hsurj w
    obtain ⟨u, hu, hqu⟩ := exists_ellX_eq (r := r) ha hx
    exact ⟨u, hu, by change G (ellX τ a r u) = G _; rw [hqu]⟩
  swap
  · exact HasLocalForm.comp (hloc _ (ellX_notMem_twoTorsionX ha hu)) (analyticAt_ellX hu)
      (deriv_ellX_ne_zero ha hu)
  -- the charts over a disc about `w`
  set n := sig w
  have hn : n ≠ 0 := (sig_pos w).ne'
  set S := {x | x ∉ Z ∧ G x = w}
  haveI : Finite S := (hfin w).to_subtype
  obtain ⟨B, hB, hBd⟩ := (hfin w).t2_separation
  have hloc' : ∀ x : S, HasLocalForm G x n := fun x ↦ by
    have hxloc := hloc x.1 x.2.1
    rwa [x.2.2] at hxloc
  choose ρ₀ hρ₀ g ψ E M hEo hEΛ hEc hEq hψ hψφ hφψ hψd hMo hxM hM using
    fun x : S ↦ exists_pointData (r := r) ha x.2.1 x.2.2 (hloc' x) (hB x).2 (hB x).1
  obtain ⟨δ, hδ, hδM⟩ := exists_dist_lt_imp_mem (isOpen_iUnion hMo) hdiff.continuousOn
    (fun x hx hGx ↦ mem_iUnion.mpr ⟨⟨x, hx, hGx⟩, hxM _⟩) hpole hinf
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 0 < ρ ∧ ρ ^ n < δ ∧ ∀ x : S, ρ ≤ ρ₀ x := by
    refine Filter.Eventually.and (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)
      (Filter.Eventually.and ?_ ?_)
    · have : Tendsto (fun ρ : ℝ ↦ ρ ^ n) (𝓝 0) (𝓝 0) := by
        simpa only [zero_pow hn] using (continuous_pow n).tendsto (0 : ℝ)
      exact nhdsWithin_le_nhds (this.eventually (gt_mem_nhds hδ))
    · exact Filter.eventually_all.mpr fun x ↦ nhdsWithin_le_nhds (Iic_mem_nhds (hρ₀ x))
  obtain ⟨ρ, hρ, hρn, hρρ⟩ := hev.exists
  set ι := S × (𝓛 τ).lattice × Bool
  set σ : ι → ℂ → ℂ := fun i y ↦ sgn i.2.2 * (y - 2 * i.2.1)
  set W : S → Set ℂ := fun x ↦ E x ∩ (fun y ↦ g x ((ellX τ a r) y)) ⁻¹' ball 0 ρ
  have h2μ : ∀ i : ι, 2 * (i.2.1 : ℂ) ∈ (𝓛 τ).lattice := fun i ↦ by
    rw [two_mul]; exact add_mem i.2.1.2 i.2.1.2
  have hσq : ∀ i y, (ellX τ a r) (σ i y) = (ellX τ a r) y := fun i y ↦ ellX_sgn _ i.2.1.2 y
  have hσv : ∀ (i : ι) (t : ℂ), σ i (sgn i.2.2 * t + 2 * i.2.1) = t := fun i t ↦ by
    simp only [σ, add_sub_cancel_right, ← mul_assoc, sgn_mul_self, one_mul]
  have hvσ : ∀ (i : ι) (y : ℂ), sgn i.2.2 * σ i y + 2 * i.2.1 = y := fun i y ↦ by
    simp only [σ, ← mul_assoc, sgn_mul_self, one_mul, sub_add_cancel]
  have hUΛ : ∀ (i : ι) y, σ i y ∈ W i.1 → y ∉ (𝓛 τ).lattice := fun i y hy hyΛ ↦
    hEΛ i.1 hy.1 (sgn_mul_mem _ (sub_mem hyΛ (h2μ i)))
  refine ⟨ρ, hρ, ι, fun i ↦ σ i ⁻¹' W i.1, fun i y ↦ g i.1 ((ellX τ a r) (σ i y)),
    fun i t ↦ sgn i.2.2 * ψ i.1 t + 2 * i.2.1, ?_, fun i ↦ ⟨fun y hy ↦ hUΛ i y hy, ?_⟩, ?_⟩
  · -- disjointness
    rintro ⟨x, μ, b⟩ ⟨x', μ', b'⟩ hij
    refine Set.disjoint_left.mpr fun y hy hy' ↦ hij ?_
    have hyB : (ellX τ a r) y ∈ B x := hσq (x, μ, b) y ▸ (hEq x _ hy.1).1
    have hyB' : (ellX τ a r) y ∈ B x' := hσq (x', μ', b') y ▸ (hEq x' _ hy'.1).1
    have hxx : x = x' := by
      by_contra hne
      exact Set.disjoint_left.mp (hBd x.2 x'.2 (Subtype.coe_ne_coe.mpr hne)) hyB hyB'
    subst hxx
    have haa : σ (x, μ, b) y = σ (x, μ', b') y := by
      rw [← hψφ x _ hy.1, ← hψφ x _ hy'.1, hσq, hσq]
    have hyΛ := hUΛ _ y hy
    simp only [σ] at haa
    simp only [sgn] at haa
    cases b <;> cases b'
    · have hμ : (μ : ℂ) = μ' := by linear_combination haa / 2
      rw [Subtype.ext hμ]
    · exfalso; apply hyΛ
      have : y = μ + μ' := by linear_combination -haa / 2
      rw [this]; exact add_mem μ.2 μ'.2
    · exfalso; apply hyΛ
      have : y = μ + μ' := by linear_combination haa / 2
      rw [this]; exact add_mem μ.2 μ'.2
    · have hμ : (μ : ℂ) = μ' := by linear_combination -haa / 2
      rw [Subtype.ext hμ]
  · -- the chart
    have hball : ball (0 : ℂ) ρ ⊆ ball 0 (ρ₀ i.1) := ball_subset_ball (hρρ i.1)
    refine ⟨((hEc i.1).isOpen_inter_preimage (hEo i.1) isOpen_ball).preimage
      (continuous_const.mul (continuous_id.sub continuous_const)), fun y hy ↦ hy.2,
      fun t ht ↦ ?_, fun y hy ↦ ?_, fun t ht ↦ ?_,
      (((hψd i.1).mono hball).const_mul _).add_const _, fun y hy ↦ ?_⟩
    · change σ i _ ∈ W i.1
      rw [hσv]
      refine ⟨hψ i.1 (hball ht), ?_⟩
      change g i.1 ((ellX τ a r) (ψ i.1 t)) ∈ ball 0 ρ
      rw [hφψ i.1 t (hball ht)]; exact ht
    · change sgn i.2.2 * ψ i.1 (g i.1 ((ellX τ a r) (σ i y))) + 2 * i.2.1 = y
      rw [hψφ i.1 _ hy.1, hvσ]
    · change g i.1 ((ellX τ a r) (σ i (sgn i.2.2 * ψ i.1 t + 2 * i.2.1))) = t
      rw [hσv, hφψ i.1 t (hball ht)]
    · have := (hEq i.1 _ hy.1).2
      change _ = w + g i.1 (ellX τ a r (σ i y)) ^ n
      rwa [hσq] at this ⊢
  · -- exhaustion
    intro y hy hFy
    have hqy : (ellX τ a r) y ∉ Z := ellX_notMem_twoTorsionX ha hy
    have hFy' : dist (G ((ellX τ a r) y)) w < ρ ^ n := hFy
    obtain ⟨x, hxM'⟩ := mem_iUnion.mp (hδM ((ellX τ a r) y) hqy (lt_trans hFy' hρn))
    obtain ⟨hGx', a', ha'E, hqa'⟩ := hM x ((ellX τ a r) y) hxM'
    have hga : g x ((ellX τ a r) y) ∈ ball 0 ρ := by
      rw [mem_ball, dist_zero_right]
      rw [hGx', dist_eq_norm, add_sub_cancel_left, norm_pow] at hFy'
      exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hρ.le hn).mp hFy'
    obtain ⟨μ, hμ, h | h⟩ := ellX_eq_or ha (hEΛ x ha'E) hy hqa'.symm
    · refine ⟨(x, ⟨μ, hμ⟩, true), ?_, ?_⟩
      · change sgn true * (y - 2 * μ) ∈ E x
        rw [h, sgn, one_mul, add_sub_cancel_right]; exact ha'E
      · change g x ((ellX τ a r) (σ (x, ⟨μ, hμ⟩, true) y)) ∈ ball 0 ρ
        rw [hσq]; exact hga
    · refine ⟨(x, ⟨μ, hμ⟩, false), ?_, ?_⟩
      · change sgn false * (y - 2 * μ) ∈ E x
        rw [h, sgn, add_sub_cancel_right, neg_one_mul, neg_neg]; exact ha'E
      · change g x ((ellX τ a r) (σ (x, ⟨μ, hμ⟩, false) y)) ∈ ball 0 ρ
        rw [hσq]; exact hga

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi
