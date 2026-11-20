/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/M2/GoodLattice.lean
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Solutions.Source_ReferenceIutCanLiftLatticeCovolume
import Solutions.Source_ReferenceIutCanLiftM2Setup

set_option autoImplicit false

open MeasureTheory Matrix Matrix.SpecialLinearGroup UpperHalfPlane Set Topology Filter
open scoped MatrixGroups Pointwise

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2

/-- A finite-index subgroup of a good lattice is a good lattice. -/
theorem GoodLattice.of_le {Γ Γ' : Subgroup SL(2, ℝ)} (h : GoodLattice Γ) (hle : Γ' ≤ Γ)
    (hidx : Γ'.relIndex Γ ≠ 0) : GoodLattice Γ' := by
  classical
  have hdisc : IsDiscrete (Γ : Set SL(2, ℝ)) := isDiscrete_iff_discreteTopology.mpr h.discrete
  refine ⟨isDiscrete_iff_discreteTopology.mp (hdisc.mono hle), ?_⟩
  obtain ⟨F, hFm, hFv, hcov, hfin⟩ := h.exists_fund
  haveI : Finite (Γ ⧸ Γ'.subgroupOf Γ) := Subgroup.index_ne_zero_iff_finite.mp hidx
  haveI := Fintype.ofFinite (Γ ⧸ Γ'.subgroupOf Γ)
  set r : Γ ⧸ Γ'.subgroupOf Γ → SL(2, ℝ) := fun q ↦ (q.out : SL(2, ℝ))
  refine ⟨⋃ q, (r q)⁻¹ • F, MeasurableSet.iUnion fun q ↦ hFm.const_smul _, ?_, ?_, ?_⟩
  · refine lt_of_le_of_lt (measure_iUnion_fintype_le _ _) ?_
    simp only [volume_smul_SL, Finset.sum_const, nsmul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) hFv
  · intro z
    obtain ⟨γ, hγ, hγz⟩ := hcov z
    set q : Γ ⧸ Γ'.subgroupOf Γ := QuotientGroup.mk ⟨γ, hγ⟩
    have hq : q.out⁻¹ * ⟨γ, hγ⟩ ∈ Γ'.subgroupOf Γ := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    refine ⟨(r q)⁻¹ * γ, hq, Set.mem_iUnion.mpr ⟨q, ?_⟩⟩
    rw [mul_smul]
    exact Set.smul_mem_smul_set hγz
  · intro z
    refine (Set.finite_iUnion fun q ↦ (hfin z).image fun g ↦ (r q)⁻¹ * g).subset ?_
    rintro γ' ⟨hγ', hz⟩
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hz
    rw [Set.mem_inv_smul_set_iff, ← mul_smul] at hq
    refine Set.mem_iUnion.mpr ⟨q, r q * γ', ⟨mul_mem q.out.2 (hle hγ'), hq⟩, ?_⟩
    simp

/-- A discrete subgroup has a neighbourhood of the identity that isolates it. -/
private theorem exists_nhds_of_discrete (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ] :
    ∃ U ∈ 𝓝 (1 : SL(2, ℝ)), ∀ γ ∈ Γ, γ ∈ U → γ = 1 := by
  have hopen : IsOpen ({1} : Set Γ) := isOpen_discrete _
  obtain ⟨U, hU, hEq⟩ := isOpen_induced_iff.mp hopen
  refine ⟨U, hU.mem_nhds ?_, fun γ hγ hγU ↦ ?_⟩
  · have : (1 : Γ) ∈ Subtype.val ⁻¹' U := by rw [hEq]; rfl
    exact this
  · have : (⟨γ, hγ⟩ : Γ) ∈ Subtype.val ⁻¹' U := hγU
    rw [hEq] at this
    exact congrArg Subtype.val this

/-- The conjugate of a translation is determined by the bottom row of the conjugator. -/
private theorem conj_translation (γ P : SL(2, ℝ)) {h : ℝ}
    (hP : (P : Matrix (Fin 2) (Fin 2) ℝ) = !![1, h; 0, 1]) :
    ((γ⁻¹ * P * γ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![1 + h * γ 1 0 * γ 1 1, h * γ 1 1 ^ 2; -h * γ 1 0 ^ 2, 1 - h * γ 1 0 * γ 1 1] := by
  have hdet := γ.det_coe
  rw [det_fin_two] at hdet
  rw [coe_mul, coe_mul, coe_inv, hP, adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination hdet
  · ring
  · ring
  · linear_combination hdet

/-- If a discrete subgroup contains a nontrivial translation, its bottom rows stay away from
zero. -/
private theorem exists_bottom_row_bound {Γ : Subgroup SL(2, ℝ)} [DiscreteTopology Γ]
    {P : SL(2, ℝ)} (hPΓ : P ∈ Γ) {h : ℝ} (hh : h ≠ 0)
    (hP : (P : Matrix (Fin 2) (Fin 2) ℝ) = !![1, h; 0, 1]) :
    ∃ δ > 0, ∀ γ ∈ Γ, δ ≤ γ 1 0 ^ 2 + γ 1 1 ^ 2 := by
  obtain ⟨U, hU, hU1⟩ := exists_nhds_of_discrete Γ
  let M : ℝ × ℝ → SL(2, ℝ) := fun p ↦
    ⟨!![1 + h * p.1 * p.2, h * p.2 ^ 2; -h * p.1 ^ 2, 1 - h * p.1 * p.2], by
      rw [det_fin_two_of]
      ring⟩
  have hMc : Continuous M := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hM0 : M (0, 0) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M]
  have hpre : M ⁻¹' U ∈ 𝓝 ((0, 0) : ℝ × ℝ) :=
    hMc.continuousAt.preimage_mem_nhds (hM0 ▸ hU)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨ε ^ 2, by positivity, fun γ hγ ↦ ?_⟩
  by_contra hlt
  push Not at hlt
  have hc : |γ 1 0| < ε := by
    have : γ 1 0 ^ 2 < ε ^ 2 := by nlinarith only [hlt, sq_nonneg (γ 1 1)]
    exact abs_lt_of_sq_lt_sq this hε.le
  have hd : |γ 1 1| < ε := by
    have : γ 1 1 ^ 2 < ε ^ 2 := by nlinarith only [hlt, sq_nonneg (γ 1 0)]
    exact abs_lt_of_sq_lt_sq this hε.le
  have hmem : ((γ 1 0, γ 1 1) : ℝ × ℝ) ∈ Metric.ball (0, 0) ε := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    simpa [Real.dist_eq] using ⟨hc, hd⟩
  have heq : M (γ 1 0, γ 1 1) = γ⁻¹ * P * γ := by
    apply Subtype.ext
    exact (conj_translation γ P hP).symm
  have h1 := hU1 _ (mul_mem (mul_mem (inv_mem hγ) hPΓ) hγ) (heq ▸ hball hmem)
  rw [← heq] at h1
  have e01 := congrArg (fun g : SL(2, ℝ) ↦ g 0 1) h1
  have e10 := congrArg (fun g : SL(2, ℝ) ↦ g 1 0) h1
  simp [M] at e01 e10
  have hdet := γ.det_coe
  rw [det_fin_two, e01.resolve_left hh, e10.resolve_left hh] at hdet
  simp at hdet

/-- A lower bound on bottom rows gives an upper bound on the heights of the orbit of a point. -/
private theorem im_smul_le_of_bound {δ : ℝ} (hδ : 0 < δ) (γ : SL(2, ℝ))
    (hγ : δ ≤ γ 1 0 ^ 2 + γ 1 1 ^ 2) (z : ℍ) :
    (γ • z).im ≤ (2 * z.im ^ 2 + 1 + 2 * z.re ^ 2) / (z.im * δ) := by
  have hheight : (γ • z).im = z.im / Complex.normSq (γ 1 0 * (z : ℂ) + γ 1 1) := by
    change (mapGL ℝ γ • z).im = _
    rw [UpperHalfPlane.im_smul_eq_div_normSq]
    simp [UpperHalfPlane.denom]
  rw [hheight]
  set c := γ 1 0
  set d := γ 1 1
  have hQ : Complex.normSq (c * (z : ℂ) + d) = (c * z.re + d) ^ 2 + (c * z.im) ^ 2 := by
    rw [Complex.normSq_apply]
    simp
    ring
  have hpos : 0 < Complex.normSq (c * (z : ℂ) + d) := by
    simpa [UpperHalfPlane.denom, c, d] using
      UpperHalfPlane.normSq_denom_pos (mapGL ℝ γ) z.im_ne_zero
  rw [div_le_div_iff₀ hpos (mul_pos z.im_pos hδ), hQ]
  have hrow : z.im ^ 2 * (c ^ 2 + d ^ 2) ≤
      ((c * z.re + d) ^ 2 + (c * z.im) ^ 2) * (2 * z.im ^ 2 + 1 + 2 * z.re ^ 2) := by
    nlinarith [sq_nonneg (2 * c * z.re + d), sq_nonneg (c * z.re + d), sq_nonneg c,
      sq_nonneg (c * z.im), sq_nonneg z.re, mul_nonneg (sq_nonneg (c * z.im)) (sq_nonneg z.re),
      mul_nonneg (sq_nonneg (c * z.re + d)) (sq_nonneg z.im)]
  have hδ' : z.im ^ 2 * δ ≤ z.im ^ 2 * (c ^ 2 + d ^ 2) :=
    mul_le_mul_of_nonneg_left hγ (sq_nonneg _)
  nlinarith only [hrow, hδ']

/-- A closed box with positive lower height is compact in the upper half-plane. -/
private theorem isCompact_box (a b η H : ℝ) (hη : 0 < η) :
    IsCompact {w : ℍ | w.re ∈ Icc a b ∧ w.im ∈ Icc η H} := by
  rw [isEmbedding_coe.isInducing.isCompact_iff]
  have hImage : ((↑) '' {w : ℍ | w.re ∈ Icc a b ∧ w.im ∈ Icc η H} : Set ℂ) =
      Complex.equivRealProdCLM.toHomeomorph ⁻¹' (Icc a b ×ˢ Icc η H) := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      simp only [Set.mem_preimage, Set.mem_prod]
      exact ⟨by simpa using hz.1, by simpa using hz.2⟩
    · intro hw
      simp only [Set.mem_preimage, Set.mem_prod] at hw
      have hwη := hw.2.1
      simp at hwη
      exact ⟨⟨w, hη.trans_le hwη⟩, by simpa using hw, rfl⟩
  rw [hImage, Homeomorph.isCompact_preimage]
  exact isCompact_Icc.prod isCompact_Icc

/-- A strip of positive lower height has finite multiplicity for a discrete subgroup containing
a nontrivial translation. -/
theorem finite_strip_multiplicity {Γ : Subgroup SL(2, ℝ)} [DiscreteTopology Γ] {P : SL(2, ℝ)}
    (hPΓ : P ∈ Γ) {h : ℝ} (hh : h ≠ 0) (hP : (P : Matrix (Fin 2) (Fin 2) ℝ) = !![1, h; 0, 1])
    (a b η : ℝ) (hη : 0 < η) (z : ℍ) :
    {γ : SL(2, ℝ) | γ ∈ Γ ∧ γ • z ∈ {w : ℍ | w.re ∈ Icc a b ∧ η ≤ w.im}}.Finite := by
  obtain ⟨δ, hδ, hb⟩ := exists_bottom_row_bound hPΓ hh hP
  set H := (2 * z.im ^ 2 + 1 + 2 * z.re ^ 2) / (z.im * δ)
  have hfin := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := Γ)
    (isCompact_singleton (x := z)) (isCompact_box a b η H hη)
  refine (hfin.image Subtype.val).subset ?_
  rintro γ ⟨hγ, hre, him⟩
  refine ⟨⟨γ, hγ⟩, ⟨γ • z, ⟨z, rfl, rfl⟩, hre, him, ?_⟩, rfl⟩
  exact im_smul_le_of_bound hδ γ (hb γ hγ) z

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2
