/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream files.

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/Fuchsian/Covolume.lean
-/
import Solutions.Source_ReferenceIutCanLiftCommensuratorIndex
import Solutions.Source_ReferenceIutCanLiftLatticeCovolume
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import Mathlib.Analysis.Real.Cardinality
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

set_option autoImplicit false

open MeasureTheory Matrix UpperHalfPlane Set Topology Filter
open scoped BigOperators MatrixGroups ENNReal NNReal Pointwise

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

/-- **Packing versus covering.** -/
private theorem volume_le_two_mul_of_packing {Γ : Subgroup SL(2, ℝ)} [Countable Γ] {U F : Set ℍ}
    (hU : MeasurableSet U) (hF : MeasurableSet F)
    (hpack : ∀ γ ∈ Γ, γ ≠ 1 → γ ≠ -1 → Disjoint (γ • U) U)
    (hcov : ∀ z : ℍ, ∃ γ ∈ Γ, γ • z ∈ F) : volume U ≤ 2 * volume F := by
  classical
  -- `U ⊆ ⋃ γ, γ⁻¹ • (γ • U ∩ F)`
  have hsub : U ⊆ ⋃ γ : Γ, (γ : SL(2, ℝ))⁻¹ • ((γ : SL(2, ℝ)) • U ∩ F) := by
    intro z hz
    obtain ⟨γ, hγ, hγz⟩ := hcov z
    refine mem_iUnion.mpr ⟨⟨γ, hγ⟩, ?_⟩
    rw [Set.mem_inv_smul_set_iff]
    exact ⟨Set.smul_mem_smul_set hz, hγz⟩
  have hmeas : ∀ γ : SL(2, ℝ), MeasurableSet (γ • U ∩ F) := fun γ ↦
    (hU.const_smul γ).inter hF
  calc volume U ≤ volume (⋃ γ : Γ, (γ : SL(2, ℝ))⁻¹ • ((γ : SL(2, ℝ)) • U ∩ F)) :=
        measure_mono hsub
    _ ≤ ∑' γ : Γ, volume ((γ : SL(2, ℝ))⁻¹ • ((γ : SL(2, ℝ)) • U ∩ F)) := measure_iUnion_le _
    _ = ∑' γ : Γ, volume ((γ : SL(2, ℝ)) • U ∩ F) := by simp_rw [volume_smul_SL]
    _ = ∑' γ : Γ, ∫⁻ x, ((γ : SL(2, ℝ)) • U ∩ F).indicator 1 x := by
        simp_rw [lintegral_indicator_one (hmeas _)]
    _ = ∫⁻ x, ∑' γ : Γ, ((γ : SL(2, ℝ)) • U ∩ F).indicator 1 x := by
        rw [lintegral_tsum fun γ ↦ (measurable_one.indicator (hmeas _)).aemeasurable]
    _ ≤ ∫⁻ x, 2 * F.indicator 1 x := by
        refine lintegral_mono fun x ↦ ?_
        by_cases hx : ∃ γ : Γ, x ∈ (γ : SL(2, ℝ)) • U ∩ F
        · obtain ⟨γ₀, hγ₀⟩ := hx
          have hxF : x ∈ F := hγ₀.2
          -- the support is contained in `{γ₀, -γ₀}`
          have hsupp : ∀ γ : Γ, γ ≠ γ₀ → (γ : SL(2, ℝ)) ≠ -(γ₀ : SL(2, ℝ)) →
              ((γ : SL(2, ℝ)) • U ∩ F).indicator (1 : ℍ → ℝ≥0∞) x = 0 := by
            intro γ h1 h2
            rw [Set.indicator_of_notMem]
            rintro ⟨hxU, -⟩
            obtain ⟨u, hu, rfl⟩ := hxU
            obtain ⟨u₀, hu₀, hu₀e⟩ := hγ₀.1
            have hd := hpack ((γ₀ : SL(2, ℝ))⁻¹ * γ) (mul_mem (inv_mem γ₀.2) γ.2)
              (by
                intro h; apply h1; ext1
                exact (inv_mul_eq_one.mp h).symm)
              (by
                intro h; apply h2
                rw [inv_mul_eq_iff_eq_mul, mul_neg_one] at h; exact h)
            refine Set.disjoint_left.mp hd (Set.smul_mem_smul_set hu) ?_
            have hu₀e' : (γ₀ : SL(2, ℝ)) • u₀ = (γ : SL(2, ℝ)) • u := hu₀e
            rw [mul_smul, ← hu₀e', inv_smul_smul]
            exact hu₀
          set γ₁ : Γ := if h : -(γ₀ : SL(2, ℝ)) ∈ Γ then ⟨_, h⟩ else γ₀ with hγ₁
          have hzero : ∀ γ ∉ ({γ₀, γ₁} : Finset Γ),
              ((γ : SL(2, ℝ)) • U ∩ F).indicator (1 : ℍ → ℝ≥0∞) x = 0 := by
            intro γ hγ
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hγ
            refine hsupp γ hγ.1 fun h ↦ hγ.2 ?_
            have hm : -(γ₀ : SL(2, ℝ)) ∈ Γ := h ▸ γ.2
            rw [hγ₁, dif_pos hm]; ext1; exact h
          rw [tsum_eq_sum (s := {γ₀, γ₁}) (fun b hb ↦ hzero b hb), Set.indicator_of_mem hxF]
          calc ∑ b ∈ ({γ₀, γ₁} : Finset Γ), ((b : SL(2, ℝ)) • U ∩ F).indicator 1 x
              ≤ ∑ b ∈ ({γ₀, γ₁} : Finset Γ), (1 : ℝ≥0∞) :=
                Finset.sum_le_sum fun b _ ↦ by unfold Set.indicator; split_ifs <;> simp
            _ ≤ 2 * 1 := by
                rw [Finset.sum_const, nsmul_eq_mul, mul_one, mul_one]
                exact_mod_cast (Finset.card_insert_le _ _).trans (by simp)
        · push Not at hx
          simp [Set.indicator_of_notMem (hx _)]
    _ = 2 * volume F := by
        rw [lintegral_const_mul _ (measurable_one.indicator hF), lintegral_indicator_one hF]

/-- Elements other than `±1` fix at most one point of `ℍ`. -/
private lemma fixed_subsingleton {g : SL(2, ℝ)} (h1 : g ≠ 1) (h2 : g ≠ -1) :
    {z : ℍ | g • z = z}.Subsingleton := by
  intro z hz w hw
  let G : GL (Fin 2) ℝ := SpecialLinearGroup.mapGL ℝ g
  have hpos : 0 < G.val.det := by simp [G]
  have hc : G ∉ Subgroup.center _ := by
    rw [GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    rintro ⟨c, hc⟩
    have e : ∀ i j, (g : Matrix (Fin 2) (Fin 2) ℝ) i j = Matrix.scalar (Fin 2) c i j := by
      intro i j; rw [hc]; simp [G]
    have hdet := g.det_coe
    rw [det_fin_two, e, e, e, e] at hdet
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, ne_eq, zero_ne_one,
      not_false_eq_true, Matrix.diagonal_apply_ne, mul_zero, sub_zero, one_ne_zero] at hdet
    have hc2 : c = 1 ∨ c = -1 := by
      have : (c - 1) * (c + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    rcases hc2 with rfl | rfl
    · apply h1; ext i j; rw [e]; fin_cases i <;> fin_cases j <;> simp
    · apply h2; ext i j; rw [e]; fin_cases i <;> fin_cases j <;> simp
  have hz' : G • z = z := hz
  have hw' : G • w = w := hw
  have hell := isElliptic_of_exists_smul_eq_self hpos hc ⟨z, hz'⟩
  rw [(gl_smul_eq_self_iff_eq_fixedPt hpos hell).mp hz',
    (gl_smul_eq_self_iff_eq_fixedPt hpos hell).mp hw']

private lemma countable_of_discrete (Δ : Subgroup SL(2, ℝ)) [DiscreteTopology Δ] : Countable Δ := by
  letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
  letI : SecondCountableTopology SL(2, ℝ) :=
    TopologicalSpace.Subtype.secondCountableTopology {M : Matrix (Fin 2) (Fin 2) ℝ | M.det = 1}
  exact TopologicalSpace.separableSpace_iff_countable.mp inferInstance

/-- `ℍ` is uncountable, so it contains a point fixed by no element of a countable set other than
`±1`. -/
private lemma exists_not_fixed {S : Set SL(2, ℝ)} (hS : S.Countable) :
    ∃ z₀ : ℍ, ∀ g ∈ S, g ≠ 1 → g ≠ -1 → g • z₀ ≠ z₀ := by
  set Bad : Set ℍ := ⋃ g ∈ {g ∈ S | g ≠ 1 ∧ g ≠ -1}, {z : ℍ | g • z = z}
  have hBad : Bad.Countable :=
    (hS.mono fun g hg ↦ hg.1).biUnion fun g hg ↦ (fixed_subsingleton hg.2.1 hg.2.2).countable
  have hne : ¬ (Set.univ : Set ℍ).Countable := by
    intro h
    apply Cardinal.not_countable_real
    let f : ℝ → ℍ := fun t ↦ ⟨t + Complex.I, by simp⟩
    have hf : Function.Injective f := by
      intro a b hab
      have := congrArg (fun z : ℍ ↦ (z : ℂ).re) hab
      simpa [f] using this
    exact (h.preimage hf).mono (by simp)
  have hcompl : (Badᶜ).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
    exact hne (h ▸ hBad)
  obtain ⟨z₀, hz₀⟩ := hcompl
  refine ⟨z₀, fun g hg h1 h2 hfix ↦ hz₀ ?_⟩
  exact Set.mem_biUnion (x := g) ⟨hg, h1, h2⟩ hfix

/-- A ball around a point with trivial stabiliser is moved off itself by every element of a
discrete subgroup other than `±1`. -/
private lemma exists_ball_disjoint (Δ : Subgroup SL(2, ℝ)) [DiscreteTopology Δ] {z₀ : ℍ}
    (hz₀ : ∀ g ∈ Δ, g ≠ 1 → g ≠ -1 → g • z₀ ≠ z₀) :
    ∃ r > 0, ∀ g ∈ Δ, (g • Metric.ball z₀ r ∩ Metric.ball z₀ r).Nonempty → g = 1 ∨ g = -1 := by
  set K := Metric.closedBall z₀ 1
  have hK : IsCompact K := isCompact_closedBall z₀ 1
  have hfin := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := Δ) hK hK
  set S' := {γ : Δ | ((fun x ↦ γ • x) '' K ∩ K).Nonempty ∧ (γ : SL(2, ℝ)) ≠ 1 ∧
    (γ : SL(2, ℝ)) ≠ -1}
  have hS' : S'.Finite := hfin.subset fun γ hγ ↦ hγ.1
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ γ ∈ S', ε < dist ((γ : SL(2, ℝ)) • z₀) z₀ := by
    rw [hS'.eventually_all]
    intro γ hγ
    have : 0 < dist ((γ : SL(2, ℝ)) • z₀) z₀ := dist_pos.mpr (hz₀ γ γ.2 hγ.2.1 hγ.2.2)
    exact eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds this)
  obtain ⟨ε, hε, hεpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have hε0 : (0 : ℝ) < ε := hεpos
  refine ⟨min (ε / 2) 1, lt_min (by linarith) one_pos, fun g hg ⟨w, hw1, hw2⟩ ↦ ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨v, hv, rfl⟩ := hw1
  have hvK : v ∈ K := Metric.ball_subset_closedBall (Metric.ball_subset_ball (min_le_right _ _) hv)
  have hgvK : g • v ∈ K :=
    Metric.ball_subset_closedBall (Metric.ball_subset_ball (min_le_right _ _) hw2)
  have hmem : (⟨g, hg⟩ : Δ) ∈ S' := by
    exact ⟨⟨g • v, ⟨v, hvK, rfl⟩, hgvK⟩, hne.1, hne.2⟩
  have hlt := hε ⟨g, hg⟩ hmem
  have h1 : dist (g • z₀) (g • v) < min (ε / 2) 1 := by
    rw [dist_smul]; rw [Metric.mem_ball] at hv; rwa [dist_comm]
  have h2 : dist (g • v) z₀ < min (ε / 2) 1 := hw2
  have := dist_triangle (g • z₀) (g • v) z₀
  have hm : min (ε / 2) 1 ≤ ε / 2 := min_le_left _ _
  simp only at hlt
  linarith

/-- Nonempty balls have positive hyperbolic area. -/
private lemma volume_ball_pos (z : ℍ) {r : ℝ} (hr : 0 < r) : 0 < volume (Metric.ball z r) := by
  rw [volume_eq_lintegral]
  have hmeas : Measurable fun w : ℂ ↦ ((((1 / ‖w.im‖₊) ^ 2 : NNReal)) : ℝ≥0∞) := by fun_prop
  rw [setLIntegral_pos_iff hmeas]
  have hopen : IsOpen ((↑) '' Metric.ball z r : Set ℂ) :=
    isOpenEmbedding_coe.isOpenMap _ Metric.isOpen_ball
  have hsub : ((↑) '' Metric.ball z r : Set ℂ) ⊆ Function.support
      fun w : ℂ ↦ ((((1 / ‖w.im‖₊) ^ 2 : NNReal)) : ℝ≥0∞) := by
    rintro _ ⟨w, -, rfl⟩
    simp [w.im_ne_zero]
  rw [Set.inter_eq_self_of_subset_right hsub]
  exact hopen.measure_pos _ ⟨z, z, Metric.mem_ball_self hr, rfl⟩

/-- A finite-covolume subgroup containing the central element `-1` has finite index in
any discrete overgroup. -/
theorem relIndex_ne_zero_of_discrete {Γ Δ : Subgroup SL(2, ℝ)} (hle : Γ ≤ Δ)
    [DiscreteTopology Δ] (hneg : (-1 : SL(2, ℝ)) ∈ Γ)
    (hΓ : HasFiniteCovolume Γ) : Γ.relIndex Δ ≠ 0 := by
  classical
  intro hinf
  rw [Subgroup.relIndex, Subgroup.index_eq_zero_iff_infinite] at hinf
  letI : Infinite (Δ ⧸ Γ.subgroupOf Δ) := hinf
  obtain ⟨F, hFm, hFvol, hcov⟩ := hΓ
  letI : Countable Δ := countable_of_discrete Δ
  letI : Countable Γ := Function.Injective.countable (Subgroup.inclusion_injective hle)
  obtain ⟨z₀, hz₀⟩ := exists_not_fixed (S := (Δ : Set SL(2, ℝ)))
    (Set.countable_coe_iff.mp inferInstance)
  obtain ⟨r, hr, hball⟩ := exists_ball_disjoint Δ (z₀ := z₀) hz₀
  let B := Metric.ball z₀ r
  have hBpos := volume_ball_pos z₀ hr
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt (b := 2 * volume F) hBpos.ne'
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hFvol.ne)
  let e := Infinite.natEmbedding (Δ ⧸ Γ.subgroupOf Δ)
  let δ : Fin n → SL(2, ℝ) := fun i ↦ ((e (i : ℕ)).out : SL(2, ℝ))⁻¹
  have hδΔ (i : Fin n) : δ i ∈ Δ := inv_mem (e (i : ℕ)).out.2
  have hdist (i j : Fin n) (hij : i ≠ j) : δ j * (δ i)⁻¹ ∉ Γ := by
    intro hmem
    apply hij
    refine Fin.ext (e.injective ?_)
    rw [← (e (i : ℕ)).out_eq, ← (e (j : ℕ)).out_eq, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [δ] using inv_mem hmem
  have hpm (g : SL(2, ℝ)) (hg : g ∈ Δ) (i j : Fin n) :
      (g • δ i • B ∩ δ j • B).Nonempty →
        δ j * (δ i)⁻¹ = g ∨ δ j * (δ i)⁻¹ = -g := by
    rintro ⟨x, hx1, hx2⟩
    obtain ⟨u, ⟨b, hb, rfl⟩, rfl⟩ := hx1
    obtain ⟨b', hb', hbe⟩ := hx2
    have hbe' : δ j • b' = g • δ i • b := hbe
    have hne : (((δ j)⁻¹ * g * δ i) • B ∩ B).Nonempty :=
      ⟨(δ j)⁻¹ • g • δ i • b, ⟨b, hb, by simp [mul_smul]⟩,
        by rw [← hbe', inv_smul_smul]; exact hb'⟩
    have he : g = δ j * ((δ j)⁻¹ * g * δ i) * (δ i)⁻¹ := by group
    rcases hball _ (mul_mem (mul_mem (inv_mem (hδΔ j)) hg) (hδΔ i)) hne with h | h
    · left
      rw [h, mul_one] at he
      exact he.symm
    · right
      rw [h] at he
      have hneg' : g = -(δ j * (δ i)⁻¹) := by simpa using he
      rw [hneg', neg_neg]
  let U := ⋃ i : Fin n, δ i • B
  have hUm : MeasurableSet U :=
    MeasurableSet.iUnion fun _ ↦ Metric.isOpen_ball.measurableSet.const_smul _
  have hneg_mem (g : SL(2, ℝ)) (hg : g ∈ Γ) : -g ∈ Γ := by
    simpa only [neg_one_mul] using mul_mem hneg hg
  have hpack (γ : SL(2, ℝ)) (hγ : γ ∈ Γ) (hγ1 : γ ≠ 1) (hγ2 : γ ≠ -1) :
      Disjoint (γ • U) U := by
    rw [Set.disjoint_iff]
    rintro x ⟨hx1, hx2⟩
    rw [Set.smul_set_iUnion] at hx1
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx1
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx2
    have h := hpm γ (hle hγ) i j ⟨x, hi, hj⟩
    by_cases hij : i = j
    · subst hij
      rcases h with h | h
      · exact hγ1 (by rw [← h, mul_inv_cancel])
      · exact hγ2 (by rw [mul_inv_cancel] at h; rw [← neg_neg γ, ← h])
    · apply hdist i j hij
      rcases h with h | h
      · rwa [h]
      · rw [h]
        exact hneg_mem γ hγ
  have hU := volume_le_two_mul_of_packing (Γ := Γ) hUm hFm hpack hcov
  have hdisj : Pairwise (Function.onFun Disjoint fun i : Fin n ↦ δ i • B) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_iff]
    rintro x ⟨hx1, hx2⟩
    have h := hpm 1 (one_mem _) i j ⟨x, by simpa using hx1, hx2⟩
    apply hdist i j hij
    rcases h with h | h
    · rw [h]
      exact one_mem _
    · rwa [h]
  have hUvol : volume U = n * volume B := by
    rw [measure_iUnion hdisj fun _ ↦ Metric.isOpen_ball.measurableSet.const_smul _]
    simp [volume_smul_SL]
  rw [hUvol] at hU
  exact (not_le.mpr hn) hU

namespace Peripheral

open AbcAdaptation.Reference.Heights Generators Subgroup.Commensurable

/-- Discreteness of the commensurator gives the index required by the invariant polynomial
for the lattice uniformization. -/
theorem closure_relIndex_commensurator_ne_zero_of_discrete {t : ℍ}
    (U : LatticeComplementCover (periodPair t))
    [DiscreteTopology (commensurator (Subgroup.closure {A U, B U}))] :
    (Subgroup.closure {A U, B U}).relIndex (commensurator (Subgroup.closure {A U, B U})) ≠ 0 := by
  let Γ := Subgroup.closure {A U, B U}
  have hdeck : U.deckGroup = IsUniformization.pmGroup (A U) (B U) := deckGroup_eq_pmGroup U
  have hcomm : commensurator Γ = commensurator U.deckGroup := by
    rw [hdeck]
    exact (IsUniformization.commensurable_closure_pmGroup (A U) (B U)).eq
  haveI : DiscreteTopology (commensurator U.deckGroup) :=
    hcomm ▸ (inferInstance : DiscreteTopology (commensurator Γ))
  have hindex : U.deckGroup.relIndex (commensurator U.deckGroup) ≠ 0 :=
    relIndex_ne_zero_of_discrete (le_commensurator U.deckGroup) U.neg_one_mem_deckGroup
      (deckGroup_hasFiniteCovolume U)
  exact (IsUniformization.relIndex_commensurator_closure_ne_zero_iff_pmGroup (A U) (B U)).mpr
    (by rwa [← hdeck])

end Peripheral
end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
