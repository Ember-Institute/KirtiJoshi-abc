/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/S1/OrbLift.lean, lines 30–184.
-/
import Solutions.Source_ReferenceIutCanLiftTakeuchiOrbifoldCover
import Solutions.Source_ReferenceIutCanLiftHolomorphicFunctions
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi

open Complex Filter Function Metric Set
open scoped Topology

section Chart

variable {p : ℂ → ℂ} {w : ℂ} {n : ℕ} {ρ : ℝ} {U : Set ℂ} {u v : ℂ → ℂ}

lemma OrbChart.injOn_v (hc : OrbChart p w n ρ U u v) : InjOn v (ball 0 ρ) := fun a ha b hb hab ↦ by
  rw [← hc.u_v a ha, ← hc.u_v b hb, hab]

lemma OrbChart.deriv_v_ne_zero (hc : OrbChart p w n ρ U u v) {t : ℂ} (ht : t ∈ ball (0 : ℂ) ρ) :
    deriv v t ≠ 0 :=
  HolomorphicFunctions.deriv_ne_zero_of_injOn hc.differentiableOn_v (isOpen_ball.mem_nhds ht) hc.injOn_v

/-- The chart coordinate `u` is holomorphic on `U`. -/
lemma OrbChart.differentiableOn_u (hc : OrbChart p w n ρ U u v) : DifferentiableOn ℂ u U := by
  intro y hy
  have ht : u y ∈ ball (0 : ℂ) ρ := hc.mapsTo_u hy
  have hball : ball (0 : ℂ) ρ ∈ 𝓝 (u y) := isOpen_ball.mem_nhds ht
  have hv := (hc.differentiableOn_v.analyticAt hball).hasStrictDerivAt
  have hleft : ∀ᶠ t in 𝓝 (u y), u (v t) = t := eventually_of_mem hball fun t ht ↦ hc.u_v t ht
  have h2 : HasStrictDerivAt u (deriv v (u y))⁻¹ (v (u y)) :=
    hv.to_local_left_inverse (hc.deriv_v_ne_zero ht) hleft
  rw [hc.v_u y hy] at h2
  exact h2.hasDerivAt.differentiableAt.differentiableWithinAt

end Chart

/-- Two analytic functions with the same `n`-th power near `z` differ by an `n`-th root of unity
near `z`. -/
private theorem exists_root_eventuallyEq {a b : ℂ → ℂ} {z : ℂ} {n : ℕ} (hn : 0 < n)
    (ha : AnalyticAt ℂ a z) (hb : AnalyticAt ℂ b z) (hab : ∀ᶠ x in 𝓝 z, a x ^ n = b x ^ n) :
    ∃ ζ ∈ Polynomial.nthRootsFinset n (1 : ℂ), ∀ᶠ x in 𝓝 z, a x = ζ * b x := by
  have hprim := Complex.isPrimitiveRoot_exp n hn.ne'
  by_contra hcon
  have hne : ∀ ζ ∈ Polynomial.nthRootsFinset n (1 : ℂ), ∀ᶠ x in 𝓝[≠] z, a x - ζ * b x ≠ 0 := by
    intro ζ hζ
    have han : AnalyticAt ℂ (fun x ↦ a x - ζ * b x) z := ha.sub (analyticAt_const.mul hb)
    rcases han.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact (hcon ⟨ζ, hζ, h.mono fun x hx ↦ sub_eq_zero.mp hx⟩).elim
    · exact h
  have hall := (Filter.eventually_all_finset _).2 hne
  have h2 : ∀ᶠ x in 𝓝[≠] z, a x ^ n = b x ^ n := nhdsWithin_le_nhds hab
  obtain ⟨x, hx1, hx2⟩ := (hall.and h2).exists
  rw [← sub_eq_zero, hprim.pow_sub_pow_eq_prod_sub_mul _ _ hn, Finset.prod_eq_zero_iff] at hx2
  obtain ⟨ζ, hζ, h0⟩ := hx2
  exact hx1 ζ hζ h0

/-- `h` is a holomorphic local lift of `f` through `p` near `z`, with values in `Y`. -/
def IsLocLift (p f : ℂ → ℂ) (Y : Set ℂ) (h : ℂ → ℂ) (z : ℂ) : Prop :=
  ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ h x ∧ h x ∈ Y ∧ p (h x) = f x

/-- The `1`-jet of `h` at `z`. -/
noncomputable def jet (h : ℂ → ℂ) (z : ℂ) : ℂ × ℂ × ℂ := (z, h z, deriv h z)

theorem jet_congr {h₁ h₂ : ℂ → ℂ} {z : ℂ} (hh : h₁ =ᶠ[𝓝 z] h₂) : jet h₁ z = jet h₂ z := by
  simp only [jet, hh.self_of_nhds, hh.deriv_eq]

theorem continuousOn_jet {h : ℂ → ℂ} {V : Set ℂ} (hd : DifferentiableOn ℂ h V) (hV : IsOpen V) :
    ContinuousOn (jet h) V :=
  continuousOn_id.prodMk (hd.continuousOn.prodMk (hd.deriv hV).continuousOn)

/-- The jets of holomorphic local lifts of `f` through `p` at points of `ℍ`. -/
def germs (p f : ℂ → ℂ) (Y : Set ℂ) : Set (ℂ × ℂ × ℂ) :=
  {q | q.1 ∈ upper ∧ ∃ h, IsLocLift p f Y h q.1 ∧ jet h q.1 = q}

theorem isLocLift_of {p f H : ℂ → ℂ} {Y V : Set ℂ} (hV : IsOpen V) (hd : DifferentiableOn ℂ H V)
    (hv : ∀ z ∈ V, H z ∈ Y ∧ p (H z) = f z) {z : ℂ} (hz : z ∈ V) : IsLocLift p f Y H z := by
  filter_upwards [hV.mem_nhds hz] with x hx
  exact ⟨hd.differentiableAt (hV.mem_nhds hx), hv x hx⟩

theorem isOpen_upper : IsOpen upper := isOpen_lt continuous_const continuous_im

variable {p f : ℂ → ℂ} {Y : Set ℂ} {e : ℂ → ℕ}

/-- **Local classification of lifts.** Near every `z₀ ∈ ℍ` the local lifts of `f` through `p` are
exactly the maps `H i ζ = v i (ζ * g)`, and at `z₀` their jets are pairwise distinct. -/
theorem orbifoldLocalLiftData (he : ∀ w, 0 < e w) (hp : IsOrbCover p Y e)
    (hf : ∀ z ∈ upper, HasLocalForm f z (e (f z))) {z₀ : ℂ} (hz₀ : z₀ ∈ upper) :
    ∃ r > (0 : ℝ), ball z₀ r ⊆ upper ∧ ∃ (ι : Type) (U : ι → Set ℂ) (K : Finset ℂ)
      (H : ι → ℂ → ℂ → ℂ), Nonempty ι ∧ (1 : ℂ) ∈ K ∧ Pairwise (Disjoint on U) ∧
      (∀ i, IsOpen (U i)) ∧ (∀ i, ∀ ζ ∈ K, DifferentiableOn ℂ (H i ζ) (ball z₀ r)) ∧
      (∀ i, ∀ ζ ∈ K, ∀ z ∈ ball z₀ r, H i ζ z ∈ U i ∧ H i ζ z ∈ Y ∧ p (H i ζ z) = f z) ∧
      (∀ z ∈ ball z₀ r, ∀ h, IsLocLift p f Y h z → ∃ i, ∃ ζ ∈ K, h =ᶠ[𝓝 z] H i ζ) ∧
      (∀ i, ∀ ζ ∈ K, ∀ ζ' ∈ K, ζ ≠ ζ' → deriv (H i ζ) z₀ ≠ deriv (H i ζ') z₀) := by
  set w := f z₀ with hw
  set n := e w with hn_def
  have hn : 0 < n := he w
  obtain ⟨⟨y₀, hy₀Y, hy₀⟩, ρ, hρ, ι, U, u, v, hdisj, hchart, hcov⟩ := hp w
  obtain ⟨g, hga, hg0, hg'0, hfg⟩ := hf z₀ hz₀
  have hup : ∀ᶠ z in 𝓝 z₀, z ∈ upper := isOpen_upper.mem_nhds hz₀
  have hgs : ∀ᶠ z in 𝓝 z₀, g z ∈ ball (0 : ℂ) ρ :=
    hga.continuousAt.eventually_mem (isOpen_ball.mem_nhds (by simpa [hg0] using hρ))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (((hup.and hga.eventually_analyticAt).and hgs).and hfg)
  set K := Polynomial.nthRootsFinset n (1 : ℂ) with hK
  have hKmem : ∀ ζ, ζ ∈ K ↔ ζ ^ n = 1 := fun ζ ↦ Polynomial.mem_nthRootsFinset hn 1
  have hmem : ∀ ζ ∈ K, ∀ z ∈ ball z₀ r, ζ * g z ∈ ball (0 : ℂ) ρ := by
    intro ζ hζ z hz
    have h1 : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one ((hKmem ζ).1 hζ) hn.ne'
    have h2 := (hball z hz).1.2
    rw [mem_ball_zero_iff] at h2 ⊢
    rwa [norm_mul, h1, one_mul]
  have hfz : ∀ z ∈ ball z₀ r, f z = w + g z ^ n := fun z hz ↦ (hball z hz).2
  refine ⟨r, hr, fun z hz ↦ (hball z hz).1.1.1, ι, U, K, fun i ζ z ↦ v i (ζ * g z), ?_, ?_,
    hdisj, fun i ↦ (hchart i).2.isOpen, ?_, ?_, ?_, ?_⟩
  · -- The fiber over `w` is nonempty.
    have : p y₀ ∈ ball w (ρ ^ n) := by rw [hy₀]; exact mem_ball_self (pow_pos hρ n)
    obtain ⟨i, -⟩ := hcov y₀ hy₀Y this
    exact ⟨i⟩
  · exact (hKmem 1).2 (one_pow n)
  · intro i ζ hζ z hz
    have hgd : DifferentiableAt ℂ g z := (hball z hz).1.1.2.differentiableAt
    have hvd : DifferentiableAt ℂ (v i) (ζ * g z) :=
      (hchart i).2.differentiableOn_v.differentiableAt (isOpen_ball.mem_nhds (hmem ζ hζ z hz))
    exact (hvd.comp z (hgd.const_mul ζ)).differentiableWithinAt
  · intro i ζ hζ z hz
    have hU : v i (ζ * g z) ∈ U i := (hchart i).2.mapsTo_v (hmem ζ hζ z hz)
    refine ⟨hU, (hchart i).1 hU, ?_⟩
    rw [(hchart i).2.eq_pow _ hU, (hchart i).2.u_v _ (hmem ζ hζ z hz), mul_pow, (hKmem ζ).1 hζ,
      one_mul, hfz z hz]
  · intro z hz h hh
    obtain ⟨hdz, hYz, hpz⟩ := hh.self_of_nhds
    have hball' : p (h z) ∈ ball w (ρ ^ n) := by
      rw [hpz, hfz z hz, mem_ball, dist_eq_norm, add_sub_cancel_left, norm_pow]
      exact pow_lt_pow_left₀ (mem_ball_zero_iff.mp (hball z hz).1.2) (norm_nonneg _) hn.ne'
    obtain ⟨i, hi⟩ := hcov (h z) hYz hball'
    have hUo := (hchart i).2.isOpen
    have hU : ∀ᶠ x in 𝓝 z, h x ∈ U i := hdz.continuousAt.eventually_mem (hUo.mem_nhds hi)
    have hbz : ∀ᶠ x in 𝓝 z, x ∈ ball z₀ r := isOpen_ball.mem_nhds hz
    have hda : ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ (fun x ↦ u i (h x)) x := by
      filter_upwards [hh, hU] with x hx hxU
      exact ((hchart i).2.differentiableOn_u.differentiableAt (hUo.mem_nhds hxU)).comp x hx.1
    have ha : AnalyticAt ℂ (fun x ↦ u i (h x)) z :=
      DifferentiableOn.analyticAt (s := {x | DifferentiableAt ℂ (fun x ↦ u i (h x)) x})
        (fun x hx ↦ DifferentiableAt.differentiableWithinAt hx) hda
    have hab : ∀ᶠ x in 𝓝 z, u i (h x) ^ n = g x ^ n := by
      filter_upwards [hh, hU, hbz] with x hx hxU hxb
      have := hx.2.2
      rw [(hchart i).2.eq_pow _ hxU, hfz x hxb] at this
      exact add_left_cancel this
    obtain ⟨ζ, hζ, hζe⟩ := exists_root_eventuallyEq hn ha (hball z hz).1.1.2 hab
    refine ⟨i, ζ, hζ, ?_⟩
    filter_upwards [hζe, hU] with x hx hxU
    rw [← hx, (hchart i).2.v_u _ hxU]
  · intro i ζ hζ ζ' hζ' hne heq
    have hz₀ : z₀ ∈ ball z₀ r := mem_ball_self hr
    have hderiv : ∀ ξ ∈ K, deriv (fun z ↦ v i (ξ * g z)) z₀ = deriv (v i) 0 * (ξ * deriv g z₀) := by
      intro ξ hξ
      have hvd : DifferentiableAt ℂ (v i) (ξ * g z₀) :=
        (hchart i).2.differentiableOn_v.differentiableAt (isOpen_ball.mem_nhds (hmem ξ hξ z₀ hz₀))
      have := hvd.hasDerivAt.comp z₀ (hga.differentiableAt.hasDerivAt.const_mul ξ)
      have h2 := this.deriv
      simp only [Function.comp_def, hg0, mul_zero] at h2
      exact h2
    rw [hderiv ζ hζ, hderiv ζ' hζ'] at heq
    have h0 : deriv (v i) 0 ≠ 0 := (hchart i).2.deriv_v_ne_zero (mem_ball_self hρ)
    exact hne (mul_right_cancel₀ hg'0 (mul_left_cancel₀ h0 heq))

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi
