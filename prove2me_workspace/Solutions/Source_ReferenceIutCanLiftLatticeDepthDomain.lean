/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original path Oka/Uniformization/Depth.lean
-/
import Solutions.Source_ReferenceIutCanLiftLatticeGenerators
import Solutions.Source_ReferenceIutCanLiftLatticeParabolicMonodromy
import Solutions.Source_ReferenceIutCanLiftOrbitDepth
import Mathlib.Topology.MetricSpace.Bounded

set_option autoImplicit false

open Complex Metric Set
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
namespace Peripheral

open AbcAdaptation.Reference.Heights Generators

variable {t : ℍ} {U : LatticeComplementCover (periodPair t)}

variable (U) in
/-- The depth for the lattice covering, based at the lift of the parallelogram center. -/
noncomputable abbrev depth (τ : ℍ) : ℝ := orbitDepth U.deckGroup (e₀ U) τ

theorem depth_le {τ : ℍ} {γ : SL(2, ℝ)} (hγ : γ ∈ U.deckGroup) :
    depth U τ ≤ dist (γ • τ) (e₀ U) := by
  have hmem : γ • τ ∈ MulAction.orbit U.deckGroup τ :=
    MulAction.mem_orbit_iff.mpr ⟨⟨γ, hγ⟩, rfl⟩
  rw [dist_comm]
  exact Metric.infDist_le_dist_of_mem hmem

theorem le_depth {τ : ℍ} {r : ℝ}
    (h : ∀ γ ∈ U.deckGroup, r ≤ dist (γ • τ) (e₀ U)) : r ≤ depth U τ := by
  change r ≤ Metric.infDist (e₀ U) (MulAction.orbit U.deckGroup τ)
  refine (Metric.le_infDist (MulAction.nonempty_orbit τ)).mpr ?_
  intro ν hν
  obtain ⟨γ, rfl⟩ := MulAction.mem_orbit_iff.mp hν
  rw [dist_comm, MulAction.subgroup_smul_def]
  exact h γ.1 γ.2

theorem depth_smul {τ : ℍ} {γ : SL(2, ℝ)} (hγ : γ ∈ U.deckGroup) :
    depth U (γ • τ) = depth U τ := by
  change Metric.infDist (e₀ U) (MulAction.orbit U.deckGroup ((⟨γ, hγ⟩ : U.deckGroup) • τ)) =
    Metric.infDist (e₀ U) (MulAction.orbit U.deckGroup τ)
  rw [MulAction.orbit_smul]

variable (t) in
/-- The fundamental parallelogram minus `ε`-discs about its corners. -/
def Kε (ε : ℝ) : Set ℂ :=
  {k | 0 ≤ cx t k ∧ cx t k ≤ 1 ∧ 0 ≤ cy t k ∧ cy t k ≤ 1 ∧
    ε ≤ dist k 0 ∧ ε ≤ dist k 1 ∧ ε ≤ dist k t ∧ ε ≤ dist k (1 + t)}

theorem isCompact_Kε (ε : ℝ) : IsCompact (Kε t ε) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · simp only [Kε, setOf_and]
    refine ((isClosed_le continuous_const (continuous_cx t)).inter
      ((isClosed_le (continuous_cx t) continuous_const).inter
      ((isClosed_le continuous_const (continuous_cy t)).inter
      ((isClosed_le (continuous_cy t) continuous_const).inter ?_))))
    exact (isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      ((isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      ((isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      (isClosed_le continuous_const (continuous_id.dist continuous_const))))
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 + ‖(t : ℂ)‖)).subset ?_
    rintro k ⟨h1, h2, h3, h4, -⟩
    rw [mem_closedBall_zero_iff, eq_cx_cy t k]
    calc ‖(cx t k : ℂ) + cy t k * t‖ ≤ ‖(cx t k : ℂ)‖ + ‖(cy t k : ℂ) * t‖ := norm_add_le _ _
      _ ≤ 1 + ‖(t : ℂ)‖ := by
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg h1,
          Real.norm_of_nonneg h3]
        have hcy : cy t k * ‖(t : ℂ)‖ ≤ ‖(t : ℂ)‖ := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right h4 (norm_nonneg (t : ℂ))
        exact add_le_add h2 hcy

theorem Kε_subset {ε : ℝ} (hε : 0 < ε) : Kε t ε ⊆ K t := by
  rintro k ⟨h1, h2, h3, h4, d0, d1, dt, d1t⟩
  rcases h3.lt_or_eq with h3 | h3
  · rcases h4.lt_or_eq with h4 | h4
    · exact Or.inl ⟨h1, h2, h3, h4⟩
    · refine Or.inr ⟨?_, ?_, h3.le, h4.le⟩
      · rcases h1.lt_or_eq with h1 | h1
        · exact h1
        · exfalso
          have : k = t := ext_cx_cy t (by rw [← h1, cx_t]) (by rw [h4, cy_t])
          rw [this, dist_self] at dt; linarith
      · rcases h2.lt_or_eq with h2 | h2
        · exact h2
        · exfalso
          have : k = 1 + t := ext_cx_cy t (by rw [h2, cx_add, cx_one, cx_t]; ring)
            (by rw [h4, cy_add, cy_one, cy_t]; ring)
          rw [this, dist_self] at d1t; linarith
  · refine Or.inr ⟨?_, ?_, h3.le, by rw [← h3]; norm_num⟩
    · rcases h1.lt_or_eq with h1 | h1
      · exact h1
      · exfalso
        have : k = 0 := ext_cx_cy t (by rw [← h1]; simp [cx, cy]) (by rw [← h3]; simp [cy])
        rw [this, dist_self] at d0; linarith
    · rcases h2.lt_or_eq with h2 | h2
      · exact h2
      · exfalso
        have : k = 1 := ext_cx_cy t (by rw [h2, cx_one]) (by rw [← h3, cy_one])
        rw [this, dist_self] at d1; linarith

theorem corner_mem_lattice : (0 : ℂ) ∈ (periodPair t).lattice ∧ (1 : ℂ) ∈ (periodPair t).lattice ∧
    (t : ℂ) ∈ (periodPair t).lattice ∧ (1 + t : ℂ) ∈ (periodPair t).lattice :=
  ⟨zero_mem _, one_mem t, t_mem t, add_mem (one_mem t) (t_mem t)⟩

/-- **Decomposition of `ℍ`.** Up to `Γ`, every point is over the compact part `Kε` or is
`Σ (log w)` with `0 < |w| < ε`. -/
theorem compact_or_cusp {ε : ℝ} (hεr : ε ≤ r₀ t) (τ : ℍ) :
    (∃ γ ∈ U.deckGroup, ∃ k ∈ Kε t ε, γ • τ = sK U k) ∨
      ∃ γ ∈ U.deckGroup, ∃ w ∈ ball (0 : ℂ) ε, w ≠ 0 ∧ γ • τ = Sig U (Complex.log w) := by
  obtain ⟨g, hg, k, hk, rfl⟩ := exists_tile U τ
  have hgi := inv_mem hg
  by_cases hkε : k ∈ Kε t ε
  · exact Or.inl ⟨g⁻¹, hgi, k, hkε, by rw [inv_smul_smul]⟩
  · right
    obtain ⟨b1, b2, b3, b4⟩ := K_bounds hk
    have : ∃ c ∈ (periodPair t).lattice, dist k c < ε := by
      simp only [Kε, mem_ofPred_eq, not_and, not_le] at hkε
      by_cases h0 : ε ≤ dist k 0
      · by_cases h1 : ε ≤ dist k 1
        · by_cases h2 : ε ≤ dist k t
          · exact ⟨_, corner_mem_lattice.2.2.2, hkε b1 b2 b3 b4 h0 h1 h2⟩
          · exact ⟨_, corner_mem_lattice.2.2.1, not_le.mp h2⟩
        · exact ⟨_, corner_mem_lattice.2.1, not_le.mp h1⟩
      · exact ⟨_, corner_mem_lattice.1, not_le.mp h0⟩
    obtain ⟨c, hc, hkc⟩ := this
    set w := k - c
    have hw0 : w ≠ 0 := fun h ↦ K_notMem_lattice t hk (by rw [sub_eq_zero.mp h]; exact hc)
    have hwε : w ∈ ball (0 : ℂ) ε := by rwa [mem_ball_zero_iff, ← dist_eq_norm]
    have hwD : w ∈ Dst t := ⟨ball_subset_ball hεr hwε, hw0⟩
    obtain ⟨γ, hγ, hγτ⟩ := U.exists_mem_deckGroup (τ := g • sK U k)
      (τ' := Sig U (Complex.log w)) (by
        rw [ψ_Sig U (log_mem_Hr hwD), Complex.exp_log hw0]
        obtain ⟨l, hl, hgl⟩ := hg
        rw [hgl, ψ_sK U hk]
        have : w - (k + l) = -(c + l) := by simp only [w]; ring
        rw [this]
        exact neg_mem (add_mem hc hl))
    exact ⟨γ, hγ, w, hwε, hw0, hγτ⟩

end Peripheral
end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
