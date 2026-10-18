/-
original-path: refer/iut/Iut/Concrete/LocalConstruct/Admissible.lean
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: fe96f99cae5c6d48d25113163f1b9b388fc35814
source-snapshot: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
license: Apache-2.0 (see project LICENSE)
modification: adapt radial membership and supremum construction to genuine
  infinite-place tensors and their actual normalized Haar. Use boundedness
  and positive Haar explicitly; derive a total radialHull with laws on
  this admissible domain. No reference LocalTheory or contracts imported.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalArchimedeanTensorHaar

/-!
source-id: JT-SCENE1-LOCAL-ARCHIMEDEAN-RADIAL-HULL
source: reference Admissible (103--178), IUT IV Proposition 1.5(iii),
Cor312/HolomorphicHull for leastness, monotonicity and fixed points.
fidelity: constructs the least positive real radial scaling of B_I for
any bounded region of positive actual Haar. Proves closure laws, compactness,
positive finite measure, exact radius-volume formula and log monotonicity.
Values outside this domain carry no hull laws. This radial hull is not a
hull among arbitrary tensor units, nor a paper theta-locus identity.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.LocalArchimedean

open NumberField MeasureTheory
open scoped Pointwise Classical

universe u
noncomputable section
variable {K : Type u} [Field K] {ι : Type} [Fintype ι] (c : ι → InfinitePlace K)

def radialRegion (t : ℝ) : Set (Tensor c) := t • archIntegral c

theorem mem_radialRegion {t : ℝ} (ht : 0 < t) {x : Tensor c} :
    x ∈ radialRegion c t ↔ archNorm c x ≤ t := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    calc
      archNorm c (t • y) ≤ |t| * archNorm c y := archNorm_smul_le c t y
      _ ≤ t * 1 := by rw [abs_of_pos ht]; exact mul_le_mul_of_nonneg_left hy ht.le
      _ = t := mul_one t
  · intro hx
    refine ⟨t⁻¹ • x, ?_, smul_inv_smul₀ ht.ne' x⟩
    change archNorm c (t⁻¹ • x) ≤ 1
    calc
      archNorm c (t⁻¹ • x) ≤ |t⁻¹| * archNorm c x := archNorm_smul_le c _ x
      _ ≤ t⁻¹ * t := by
        rw [abs_of_pos (inv_pos.mpr ht)]
        exact mul_le_mul_of_nonneg_left hx (inv_pos.mpr ht).le
      _ = 1 := inv_mul_cancel₀ ht.ne'

theorem radialRegion_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    radialRegion c s ⊆ radialRegion c t :=
  fun _ hx => (mem_radialRegion c (hs.trans_le hst)).mpr
    (((mem_radialRegion c hs).mp hx).trans hst)

theorem radialRegion_isCompact (t : ℝ) : IsCompact (radialRegion c t) :=
  (isCompact_archIntegral c).smul t

theorem normalizedHaar_radialRegion {t : ℝ} (ht : 0 < t) :
    normalizedHaar c (radialRegion c t) =
      ENNReal.ofReal (t ^ Module.finrank ℝ (Tensor c)) := by
  rw [radialRegion, Measure.addHaar_smul_of_nonneg (normalizedHaar c) ht.le,
    normalizedHaar_archIntegral, mul_one]

theorem radialRegion_haar_pos_lt_top {t : ℝ} (ht : 0 < t) :
    0 < normalizedHaar c (radialRegion c t) ∧
      normalizedHaar c (radialRegion c t) < ⊤ := by
  rw [normalizedHaar_radialRegion c ht]
  exact ⟨ENNReal.ofReal_pos.mpr (pow_pos ht _), ENNReal.ofReal_lt_top⟩

def hullRadius (U : Set (Tensor c)) : ℝ := sSup (archNorm c '' U)

def radialHull (U : Set (Tensor c)) : Set (Tensor c) := radialRegion c (hullRadius c U)

theorem nonempty_of_haar_pos {U : Set (Tensor c)} (hpos : 0 < normalizedHaar c U) :
    U.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty.mp h, measure_empty] at hpos
  exact (lt_irrefl _ hpos)

theorem archNorm_image_bddAbove {U : Set (Tensor c)} (hU : Bornology.IsBounded U) :
    BddAbove (archNorm c '' U) :=
  ((hU.isCompact_closure).image (continuous_archNorm c)).bddAbove.mono
    (Set.image_mono subset_closure)

theorem archNorm_le_hullRadius {U : Set (Tensor c)} (hU : Bornology.IsBounded U)
    {x : Tensor c} (hx : x ∈ U) : archNorm c x ≤ hullRadius c U :=
  le_csSup (archNorm_image_bddAbove c hU) ⟨x, hx, rfl⟩

theorem hullRadius_pos {U : Set (Tensor c)} (hU : Bornology.IsBounded U)
    (hpos : 0 < normalizedHaar c U) : 0 < hullRadius c U := by
  obtain ⟨x, hx⟩ := nonempty_of_haar_pos c hpos
  have hnonneg : 0 ≤ hullRadius c U :=
    (archNorm_nonneg c x).trans (archNorm_le_hullRadius c hU hx)
  rcases hnonneg.lt_or_eq with h | h
  · exact h
  exfalso
  have hsub : U ⊆ {0} := by
    intro y hy
    have hn : archNorm c y = 0 :=
      le_antisymm ((archNorm_le_hullRadius c hU hy).trans h.symm.le) (archNorm_nonneg c y)
    obtain ⟨C, _, hC⟩ := exists_norm_le_archNorm c
    have hz : ‖y‖ ≤ 0 := by simpa only [hn, mul_zero] using hC y
    exact norm_le_zero_iff.mp hz
  have : Nontrivial (Tensor c) := Module.nontrivial_of_finrank_pos (tensor_finrank_pos c)
  have hzero : normalizedHaar c U = 0 :=
    le_antisymm ((measure_mono hsub).trans_eq (measure_singleton (0 : Tensor c))) bot_le
  rw [hzero] at hpos
  exact (lt_irrefl _ hpos)

theorem subset_radialHull {U : Set (Tensor c)} (hU : Bornology.IsBounded U)
    (hpos : 0 < normalizedHaar c U) : U ⊆ radialHull c U :=
  fun _ hx => (mem_radialRegion c (hullRadius_pos c hU hpos)).mpr
    (archNorm_le_hullRadius c hU hx)

theorem hullRadius_le_of_subset_radialRegion {U : Set (Tensor c)}
    (hpos : 0 < normalizedHaar c U) {t : ℝ} (ht : 0 < t)
    (hUt : U ⊆ radialRegion c t) : hullRadius c U ≤ t := by
  apply csSup_le ((nonempty_of_haar_pos c hpos).image _)
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_radialRegion c ht).mp (hUt hx)

theorem radialHull_le_radialRegion {U : Set (Tensor c)} (hU : Bornology.IsBounded U)
    (hpos : 0 < normalizedHaar c U) {t : ℝ} (ht : 0 < t)
    (hUt : U ⊆ radialRegion c t) : radialHull c U ⊆ radialRegion c t :=
  radialRegion_mono c (hullRadius_pos c hU hpos)
    (hullRadius_le_of_subset_radialRegion c hpos ht hUt)

theorem radialHull_isCompact (U : Set (Tensor c)) : IsCompact (radialHull c U) :=
  radialRegion_isCompact c _

theorem radialHull_haar_pos_lt_top {U : Set (Tensor c)} (hU : Bornology.IsBounded U)
    (hpos : 0 < normalizedHaar c U) :
    0 < normalizedHaar c (radialHull c U) ∧ normalizedHaar c (radialHull c U) < ⊤ :=
  radialRegion_haar_pos_lt_top c (hullRadius_pos c hU hpos)

theorem radialHull_mono {U V : Set (Tensor c)} (hU : Bornology.IsBounded U)
    (hUpos : 0 < normalizedHaar c U) (hV : Bornology.IsBounded V)
    (hVpos : 0 < normalizedHaar c V) (hUV : U ⊆ V) : radialHull c U ⊆ radialHull c V :=
  radialHull_le_radialRegion c hU hUpos (hullRadius_pos c hV hVpos)
    (hUV.trans (subset_radialHull c hV hVpos))

theorem radialHull_radialRegion {t : ℝ} (ht : 0 < t) :
    radialHull c (radialRegion c t) = radialRegion c t :=
  Set.Subset.antisymm
    (radialHull_le_radialRegion c (radialRegion_isCompact c t).isBounded
      (radialRegion_haar_pos_lt_top c ht).1 ht Set.Subset.rfl)
    (subset_radialHull c (radialRegion_isCompact c t).isBounded
      (radialRegion_haar_pos_lt_top c ht).1)

theorem radialHull_idem {U : Set (Tensor c)} (hU : Bornology.IsBounded U)
    (hpos : 0 < normalizedHaar c U) : radialHull c (radialHull c U) = radialHull c U :=
  radialHull_radialRegion c (hullRadius_pos c hU hpos)

theorem radialHull_eq_sInter {U : Set (Tensor c)} (hU : Bornology.IsBounded U)
    (hpos : 0 < normalizedHaar c U) :
    radialHull c U = ⋂₀ {R | ∃ t : ℝ, 0 < t ∧ R = radialRegion c t ∧ U ⊆ R} := by
  apply Set.Subset.antisymm
  · intro x hx
    apply Set.mem_sInter.mpr
    rintro R ⟨t, ht, rfl, hUt⟩
    exact radialHull_le_radialRegion c hU hpos ht hUt hx
  · intro x hx
    exact Set.mem_sInter.mp hx _
      ⟨hullRadius c U, hullRadius_pos c hU hpos, rfl, subset_radialHull c hU hpos⟩

theorem normalizationLogVolume_mono {U V : Set (Tensor c)} (hUV : U ⊆ V)
    (hpos : 0 < normalizedHaar c U) (hfin : normalizedHaar c V ≠ ⊤) :
    normalizationLogVolume c U ≤ normalizationLogVolume c V := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Real.log_le_log
  · exact ENNReal.toReal_pos hpos.ne' (ne_top_of_le_ne_top hfin (measure_mono hUV))
  · exact ENNReal.toReal_mono hfin (measure_mono hUV)

theorem normalizationLogVolume_radialRegion {t : ℝ} (ht : 0 < t) :
    normalizationLogVolume c (radialRegion c t) = Real.log t := by
  unfold normalizationLogVolume
  rw [normalizedHaar_radialRegion c ht, ENNReal.toReal_ofReal (pow_nonneg ht.le _), Real.log_pow]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast (tensor_finrank_pos c).ne')

theorem normalizationLogVolume_radialHull {U : Set (Tensor c)} (hU : Bornology.IsBounded U)
    (hpos : 0 < normalizedHaar c U) :
    normalizationLogVolume c (radialHull c U) = Real.log (hullRadius c U) :=
  normalizationLogVolume_radialRegion c (hullRadius_pos c hU hpos)

theorem normalizationLogVolume_le_radialHull {U : Set (Tensor c)} (hU : Bornology.IsBounded U)
    (hpos : 0 < normalizedHaar c U) :
    normalizationLogVolume c U ≤ normalizationLogVolume c (radialHull c U) :=
  normalizationLogVolume_mono c (subset_radialHull c hU hpos) hpos
    (radialHull_haar_pos_lt_top c hU hpos).2.ne

theorem radialHull_archLogShell : radialHull c (archLogShell c) = archLogShell c :=
  radialHull_radialRegion c (pow_pos Real.pi_pos _)

end
end JoshiTeich.Act1Scene1.LocalArchimedean
