import Solutions.Source_ReferenceHeightsLatticePointMap
import Mathlib.Tactic.LinearCombination

/-!
# Surjectivity of the Weierstrass point map

The proof adapts `Heights/WeierstrassSurjectivity.lean` at
`721496ca4c158e511d25d8ccf6bfe8503eda73c1`. Liouville's theorem gives
every finite value of `℘`. The cubic relation and the parity of the two
coordinates supply a preimage of each affine point.
-/

set_option autoImplicit false

open Set Filter Topology
open scoped UpperHalfPlane

noncomputable section

namespace AbcAdaptation.Reference.Heights

open WeierstrassCurve
open AbcAdaptation.Reference.Iut.Anabelian (some_ext)

private noncomputable def reciprocalWeierstrassSub (L : PeriodPair) (a z : ℂ) : ℂ := by
  classical
  exact if z ∈ L.lattice then 0 else (L.weierstrassP z - a)⁻¹

private theorem reciprocalWeierstrassSub_analyticAt (L : PeriodPair) (a z : ℂ)
    (ha : ∀ w, w ∉ L.lattice → L.weierstrassP w ≠ a) :
    AnalyticAt ℂ (reciprocalWeierstrassSub L a) z := by
  classical
  by_cases hz : z ∈ L.lattice
  · have hevent : reciprocalWeierstrassSub L a =ᶠ[𝓝[≠] z]
        (fun w ↦ (L.weierstrassP w - a)⁻¹) := by
      have hlocal : ∀ᶠ w : ℂ in 𝓝[≠] z, w ∉ L.lattice := by
        have hlocal' : ∀ᶠ w : ℂ in 𝓝[≠] z,
            w ∈ ((L.lattice : Set ℂ) \ {z})ᶜ :=
          Filter.Eventually.filter_mono inf_le_left
            (L.compl_lattice_sdiff_singleton_mem_nhds z)
        filter_upwards [hlocal', self_mem_nhdsWithin] with w hw hwz
        intro hwl
        exact hw ⟨hwl, hwz⟩
      filter_upwards [hlocal] with w hw
      simp [reciprocalWeierstrassSub, hw]
    have hsub : meromorphicOrderAt (fun w ↦ L.weierstrassP w - a) z = -2 := by
      rw [show (fun w ↦ L.weierstrassP w - a) =
          L.weierstrassP + fun _ ↦ -a by
            funext w
            exact sub_eq_add_neg _ _]
      rw [meromorphicOrderAt_add_eq_left_of_lt (MeromorphicAt.const (-a) z) (by
        rw [L.order_weierstrassP z hz, meromorphicOrderAt_const]
        split_ifs
        · exact WithTop.coe_lt_top _
        · exact WithTop.coe_lt_coe.mpr (by norm_num))]
      exact L.order_weierstrassP z hz
    apply AnalyticAt.of_meromorphicOrderAt_pos
    · rw [meromorphicOrderAt_congr hevent]
      change 0 < meromorphicOrderAt ((fun w ↦ L.weierstrassP w - a)⁻¹) z
      rw [meromorphicOrderAt_inv, hsub]
      norm_num
    · simp [reciprocalWeierstrassSub, hz]
  · have hne : L.weierstrassP z - a ≠ 0 := sub_ne_zero.mpr (ha z hz)
    have hraw : AnalyticAt ℂ (L.weierstrassP - fun _ ↦ a)⁻¹ z :=
      ((L.analyticOnNhd_weierstrassP z hz).sub analyticAt_const).inv hne
    apply hraw.congr
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    have hw' : w ∉ L.lattice := hw
    rw [reciprocalWeierstrassSub, if_neg hw', Pi.inv_apply, Pi.sub_apply]

private theorem reciprocalWeierstrassSub_add_lattice (L : PeriodPair) (a z : ℂ)
    (l : L.lattice) :
    reciprocalWeierstrassSub L a (z + l) = reciprocalWeierstrassSub L a z := by
  classical
  by_cases hz : z ∈ L.lattice
  · have hzl : z + (l : ℂ) ∈ L.lattice := add_mem hz l.2
    simp [reciprocalWeierstrassSub, hz, hzl]
  · have hzl : z + (l : ℂ) ∉ L.lattice := by
      intro h
      exact hz ((L.lattice.toAddSubgroup.add_mem_cancel_right l.2).mp h)
    simp [reciprocalWeierstrassSub, hz, hzl, L.weierstrassP_add_coe]

/-- Every complex value is attained by `℘` away from the period lattice. -/
theorem exists_notMem_lattice_weierstrassP_eq (L : PeriodPair) (a : ℂ) :
    ∃ z, z ∉ L.lattice ∧ L.weierstrassP z = a := by
  classical
  by_contra h
  simp only [not_exists, not_and] at h
  have han : ∀ z, AnalyticAt ℂ (reciprocalWeierstrassSub L a) z :=
    fun z ↦ reciprocalWeierstrassSub_analyticAt L a z h
  have hdiff : Differentiable ℂ (reciprocalWeierstrassSub L a) :=
    fun z ↦ (han z).differentiableAt
  have hcompact : IsCompact (Set.range (reciprocalWeierstrassSub L a)) := by
    apply IsZLattice.isCompact_range_of_periodic L.lattice _ hdiff.continuous
    intro z w hw
    exact reciprocalWeierstrassSub_add_lattice L a z ⟨w, hw⟩
  let z₀ : ℂ := L.ω₁ / 2
  have hz₀ : z₀ ∉ L.lattice := L.ω₁_div_two_notMem_lattice
  have hne : reciprocalWeierstrassSub L a z₀ ≠ 0 := by
    rw [reciprocalWeierstrassSub, if_neg hz₀]
    exact inv_ne_zero (sub_ne_zero.mpr (h z₀ hz₀))
  apply hne
  exact (hdiff.apply_eq_apply_of_bounded hcompact.isBounded z₀ 0).trans (by
    simp [reciprocalWeierstrassSub, L.lattice.zero_mem])

private theorem latticePointMap_eq_some_of_coordinates (τ : ℍ) (z x y : ℂ)
    (hz : z ∉ (periodPair τ).lattice) (hxy : (latticeCurve τ).toAffine.Nonsingular x y)
    (hx : (periodPair τ).weierstrassP z = x)
    (hy : (periodPair τ).derivWeierstrassP z / 2 = y) :
    latticePointMap τ z = Affine.Point.some x y hxy := by
  rw [latticePointMap_of_notMem (τ := τ) hz]
  exact some_ext hx hy

/-- The total point-valued Weierstrass map is onto the short lattice curve. -/
theorem latticePointMap_surjective (τ : ℍ) : Function.Surjective (latticePointMap τ) := by
  intro P
  cases P with
  | zero =>
      refine ⟨0, ?_⟩
      rw [← Affine.Point.zero_def]
      exact latticePointMap_of_mem (τ := τ) (zero_mem _)
  | some x y hxy =>
      let L := periodPair τ
      obtain ⟨z, hz, hx⟩ := exists_notMem_lattice_weierstrassP_eq L x
      have heqn := hxy.1
      rw [Affine.equation_iff] at heqn
      simp only [latticeCurve, zero_mul, add_zero] at heqn
      change y ^ 2 = x ^ 3 + (-L.g₂ / 4) * x + -L.g₃ / 4 at heqn
      have hcubic := L.derivWeierstrassP_sq z hz
      rw [hx] at hcubic
      have hsq : (L.derivWeierstrassP z / 2) ^ 2 = y ^ 2 := by
        linear_combination hcubic / 4 - heqn
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hy | hy
      · exact ⟨z, latticePointMap_eq_some_of_coordinates τ z x y hz hxy hx hy⟩
      · have hnz : -z ∉ L.lattice := by simpa only [neg_mem_iff] using hz
        have hnx : L.weierstrassP (-z) = x := by
          rwa [L.weierstrassP_neg]
        have hny : L.derivWeierstrassP (-z) / 2 = y := by
          simp only [L.derivWeierstrassP_neg, neg_div, hy, neg_neg]
        exact ⟨-z, latticePointMap_eq_some_of_coordinates τ (-z) x y hnz hxy hnx hny⟩

/-- The descended point map from the complex lattice quotient is surjective. -/
theorem latticeQuotientPointMap_surjective (τ : ℍ) :
    Function.Surjective (latticeQuotientPointMap τ) := by
  intro P
  obtain ⟨z, hz⟩ := latticePointMap_surjective τ P
  exact ⟨QuotientAddGroup.mk z, (latticeQuotientPointMap_mk τ z).trans hz⟩

end AbcAdaptation.Reference.Heights
