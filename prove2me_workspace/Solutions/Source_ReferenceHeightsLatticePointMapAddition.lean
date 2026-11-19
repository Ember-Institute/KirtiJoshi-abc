import Solutions.Source_ReferenceHeightsWeierstrassAddition
import Solutions.Source_ReferenceHeightsLatticePointMapInjectivity
import Solutions.Source_ReferenceHeightsWeierstrassSurjectivity
import Mathlib.Tactic.Abel

/-!
# Additivity and uniformization of the lattice point map

The proof adapts `Heights/LatticePointMapAddition.lean` at
`721496ca4c158e511d25d8ccf6bfe8503eda73c1`. The global secant formulas
supply the addition law at distinct first coordinates. An auxiliary point
reduces doubling to secant additions.
-/

set_option autoImplicit false

namespace AbcAdaptation.Reference.Heights

open Set WeierstrassCurve
open AbcAdaptation.Reference.Iut.Anabelian (some_ext)
open scoped UpperHalfPlane Classical

private theorem latticePointMap_neg (τ : ℍ) (z : ℂ) :
    latticePointMap τ (-z) = -latticePointMap τ z := by
  let L := periodPair τ
  by_cases hz : z ∈ L.lattice
  · have hnz : -z ∈ L.lattice := neg_mem hz
    rw [latticePointMap_of_mem (τ := τ) hnz, latticePointMap_of_mem (τ := τ) hz, neg_zero]
  · have hnz : -z ∉ L.lattice := by simpa only [neg_mem_iff] using hz
    rw [latticePointMap_of_notMem (τ := τ) hnz, latticePointMap_of_notMem (τ := τ) hz,
      Affine.Point.neg_some]
    refine some_ext (L.weierstrassP_neg z) ?_
    simpa only [Affine.negY, latticeCurve, zero_mul, sub_zero, neg_div] using
      congrArg (fun y : ℂ => y / 2) ((periodPair τ).derivWeierstrassP_neg z)

private theorem latticePointMap_add_of_notMem_of_weierstrassP_ne (τ : ℍ) (z w : ℂ)
    (hz : z ∉ (periodPair τ).lattice)
    (hw : w ∉ (periodPair τ).lattice)
    (hzw : z + w ∉ (periodPair τ).lattice)
    (hne : (periodPair τ).weierstrassP z ≠ (periodPair τ).weierstrassP w) :
    latticePointMap τ (z + w) = latticePointMap τ z + latticePointMap τ w := by
  let L := periodPair τ
  have hadd := weierstrass_addition_coordinates L z w hz hw hzw hne
  have hslope :
      (latticeCurve τ).toAffine.slope (L.weierstrassP z) (L.weierstrassP w)
        (L.derivWeierstrassP z / 2) (L.derivWeierstrassP w / 2) =
      weierstrassSecantSlope L (L.weierstrassP w) (L.derivWeierstrassP w) z := by
    dsimp only [L]
    rw [Affine.slope_of_X_ne hne, weierstrassSecantSlope, ← sub_div, div_div]
  rw [latticePointMap_of_notMem (τ := τ) hzw, latticePointMap_of_notMem (τ := τ) hz,
    latticePointMap_of_notMem (τ := τ) hw, Affine.Point.add_of_X_ne hne]
  apply some_ext
  · rw [← hadd.1, hslope]
    simp only [L, Affine.addX, latticeCurve, zero_mul, add_zero, sub_zero,
      weierstrassSecantAddX]
  · rw [← hadd.2, hslope]
    simp only [L, Affine.addY, Affine.negY, Affine.negAddY, Affine.addX, latticeCurve,
      zero_mul, add_zero, sub_zero, weierstrassSecantAddY, weierstrassSecantAddX]
    ring

private theorem latticePointMap_add_self_of_notMem (τ : ℍ) (z : ℂ)
    (hz : z ∉ (periodPair τ).lattice)
    (hzz : z + z ∉ (periodPair τ).lattice) :
    latticePointMap τ (z + z) = latticePointMap τ z + latticePointMap τ z := by
  let L := periodPair τ
  let A : Set ℂ := L.lattice
  let B : Set ℂ := (fun r : ℂ ↦ z + r) ⁻¹' (L.lattice : Set ℂ)
  let C : Set ℂ := (fun r : ℂ ↦ z - r) ⁻¹' (L.lattice : Set ℂ)
  let D : Set ℂ := (fun r : ℂ ↦ r + r) ⁻¹' (L.lattice : Set ℂ)
  let S : Set ℂ := ((A ∪ B) ∪ C) ∪ D
  have hL : (L.lattice : Set ℂ).Countable :=
    countable_of_Lindelof_of_discrete (X := L.lattice)
  have hB : B.Countable := hL.preimage (add_right_injective z)
  have hC : C.Countable := hL.preimage sub_right_injective
  have hD : D.Countable := hL.preimage fun x y h ↦ by
    linear_combination h / 2
  have hS : S.Countable := ((hL.union hB).union hC).union hD
  obtain ⟨t, ht⟩ : ∃ t : ℝ, Complex.ofRealCLM t ∉ S := by
    by_contra h
    push Not at h
    have hpre : ((fun t : ℝ ↦ Complex.ofRealCLM t) ⁻¹' S).Countable :=
      hS.preimage Complex.ofReal_injective
    have hall : (fun t : ℝ ↦ Complex.ofRealCLM t) ⁻¹' S = Set.univ :=
      Set.eq_univ_of_forall h
    rw [hall] at hpre
    exact Set.not_countable_univ hpre
  let r : ℂ := Complex.ofRealCLM t
  have houtside : r ∉ L.lattice ∧ z + r ∉ L.lattice ∧ z - r ∉ L.lattice ∧
      r + r ∉ L.lattice := by
    change r ∉ S at ht
    simpa only [S, A, B, C, D, Set.mem_union, Set.mem_preimage, SetLike.mem_coe,
      not_or, and_assoc] using ht
  obtain ⟨hr, hzr, hzmr, hrr⟩ := houtside
  have hPr : L.weierstrassP z ≠ L.weierstrassP r := by
    intro hp
    exact ((weierstrassP_eq_iff_sub_mem_or_add_mem L z r hz hr).1 hp).elim hzmr hzr
  have hPnr : L.weierstrassP z ≠ L.weierstrassP (-r) := by
    rwa [L.weierstrassP_neg]
  have hnrl : -r ∉ L.lattice := by simpa only [neg_mem_iff] using hr
  have hzneg : z + -r ∉ L.lattice := by simpa only [sub_eq_add_neg] using hzmr
  have hadd₁ := latticePointMap_add_of_notMem_of_weierstrassP_ne τ z r hz hr hzr hPr
  have hadd₂ := latticePointMap_add_of_notMem_of_weierstrassP_ne τ z (-r) hz hnrl hzneg hPnr
  have hPsum : L.weierstrassP (z + r) ≠ L.weierstrassP (z - r) := by
    intro hp
    rcases (weierstrassP_eq_iff_sub_mem_or_add_mem L (z + r) (z - r) hzr hzmr).1 hp with hm | hm
    · exact hrr (by convert hm using 1 <;> ring)
    · exact hzz (by convert hm using 1 <;> ring)
  have hsum : (z + r) + (z - r) = z + z := by ring
  have hsum_notMem : (z + r) + (z - r) ∉ L.lattice := by
    rwa [hsum]
  have hadd₃ :=
    latticePointMap_add_of_notMem_of_weierstrassP_ne τ (z + r) (z - r) hzr hzmr hsum_notMem hPsum
  calc
    latticePointMap τ (z + z) = latticePointMap τ ((z + r) + (z - r)) :=
      congrArg (latticePointMap τ) hsum.symm
    _ = latticePointMap τ (z + r) + latticePointMap τ (z - r) := hadd₃
    _ = (latticePointMap τ z + latticePointMap τ r) +
        (latticePointMap τ z + latticePointMap τ (-r)) := by
      rw [hadd₁, sub_eq_add_neg, hadd₂]
    _ = latticePointMap τ z + latticePointMap τ z := by
      rw [latticePointMap_neg]
      abel

/-- The total Weierstrass point map respects addition. -/
theorem latticePointMap_add (τ : ℍ) (z w : ℂ) :
    latticePointMap τ (z + w) = latticePointMap τ z + latticePointMap τ w := by
  let L := periodPair τ
  by_cases hz : z ∈ L.lattice
  · rw [latticePointMap_of_mem (τ := τ) hz, zero_add]
    exact (latticePointMap_eq_iff_sub_mem τ (z + w) w).mpr (by convert hz using 1 <;> ring)
  by_cases hw : w ∈ L.lattice
  · rw [latticePointMap_of_mem (τ := τ) hw, add_zero]
    exact (latticePointMap_eq_iff_sub_mem τ (z + w) z).mpr (by convert hw using 1 <;> ring)
  by_cases hzw : z + w ∈ L.lattice
  · have hmap : latticePointMap τ w = latticePointMap τ (-z) :=
      (latticePointMap_eq_iff_sub_mem τ w (-z)).mpr (by convert hzw using 1 <;> ring)
    rw [latticePointMap_of_mem (τ := τ) hzw, hmap, latticePointMap_neg, add_neg_cancel]
  by_cases hp : L.weierstrassP z = L.weierstrassP w
  · have hsub : z - w ∈ L.lattice :=
      ((weierstrassP_eq_iff_sub_mem_or_add_mem L z w hz hw).mp hp).resolve_right hzw
    have hwz : w - z ∈ L.lattice := by
      simpa only [neg_sub] using neg_mem hsub
    have hmap := (latticePointMap_eq_iff_sub_mem τ w z).mpr hwz
    have hsum : latticePointMap τ (z + w) = latticePointMap τ (z + z) :=
      (latticePointMap_eq_iff_sub_mem τ (z + w) (z + z)).mpr (by convert hwz using 1 <;> ring)
    have hzz : z + z ∉ L.lattice := by
      intro htwo
      exact hzw (by convert sub_mem htwo hsub using 1 <;> ring)
    rw [hsum, hmap]
    exact latticePointMap_add_self_of_notMem τ z hz hzz
  · exact latticePointMap_add_of_notMem_of_weierstrassP_ne τ z w hz hw hzw hp

/-- The uniformization of the short lattice curve by the actual Weierstrass point map. -/
theorem latticePointUniformization (τ : ℍ) : LatticePointUniformization τ :=
  latticePointUniformization_of_add_surjective (latticePointMap_add τ)
    (latticeQuotientPointMap_surjective τ)

end AbcAdaptation.Reference.Heights
