/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original path Oka/Uniformization/Depth.lean
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.GroupTheory.Commensurable
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

open UpperHalfPlane
open scoped BigOperators MatrixGroups Pointwise

private theorem exists_finset_conj_representatives {G : Type*} [Group G]
    {Γ : Subgroup G} {δ : G} (hδ : δ ∈ Subgroup.Commensurable.commensurator Γ) :
    ∃ R : Finset G, ∀ γ ∈ Γ, ∃ g ∈ R, δ * (g⁻¹ * γ) * δ⁻¹ ∈ Γ := by
  classical
  let Δ : Subgroup G := ConjAct.toConjAct δ⁻¹ • Γ
  let H : Subgroup Γ := Δ.subgroupOf Γ
  have hδinv : δ⁻¹ ∈ Subgroup.Commensurable.commensurator Γ :=
    (Subgroup.Commensurable.commensurator Γ).inv_mem hδ
  have hindex : H.index ≠ 0 :=
    ((Subgroup.Commensurable.commensurator_mem_iff Γ δ⁻¹).mp hδinv).1
  let : Fintype (Γ ⧸ H) := Subgroup.fintypeOfIndexNeZero (H := H) hindex
  let rep : (Γ ⧸ H) → G := fun q ↦ ((q.out : Γ) : G)
  refine ⟨Finset.univ.image rep, ?_⟩
  intro γ hγ
  let γ' : Γ := ⟨γ, hγ⟩
  let q : Γ ⧸ H := QuotientGroup.mk γ'
  have hq : (QuotientGroup.mk q.out : Γ ⧸ H) = QuotientGroup.mk γ' :=
    QuotientGroup.out_eq' q
  have hsub : q.out⁻¹ * γ' ∈ Δ.subgroupOf Γ := QuotientGroup.eq.mp hq
  have hmem : ((q.out⁻¹ * γ' : Γ) : G) ∈ Δ := Subgroup.mem_subgroupOf.mp hsub
  change (rep q)⁻¹ * γ ∈ ConjAct.toConjAct δ⁻¹ • Γ at hmem
  rw [ConjAct.toConjAct_inv, Subgroup.mem_inv_pointwise_smul_iff, ConjAct.toConjAct_smul] at hmem
  exact ⟨rep q, Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩, hmem⟩

private theorem exists_infDist_orbit_smul_le {G X : Type*} [Group G] [PseudoMetricSpace X]
    [MulAction G X] [IsIsometricSMul G X] (Γ : Subgroup G) (o : X) (δ : G)
    (R : Finset G) (hR : ∀ γ ∈ Γ, ∃ g ∈ R, δ * (g⁻¹ * γ) * δ⁻¹ ∈ Γ) :
    ∃ c : ℝ, ∀ τ : X, Metric.infDist o (MulAction.orbit Γ (δ • τ)) ≤
      Metric.infDist o (MulAction.orbit Γ τ) + c := by
  let c : ℝ := ∑ g ∈ R, dist o (g • o)
  refine ⟨c + dist (δ⁻¹ • o) o, fun τ ↦ sub_le_iff_le_add.mp ?_⟩
  have hne : (MulAction.orbit Γ τ).Nonempty := MulAction.nonempty_orbit τ
  refine (Metric.le_infDist hne).mpr ?_
  intro z hz
  obtain ⟨γ, rfl⟩ := MulAction.mem_orbit_iff.mp hz
  rw [MulAction.subgroup_smul_def]
  obtain ⟨g, hg, hΓ⟩ := hR (γ : G) γ.2
  let h : G := g⁻¹ * (γ : G)
  have hmem : δ • (h • τ) ∈ MulAction.orbit Γ (δ • τ) := by
    refine MulAction.mem_orbit_iff.mpr ⟨⟨δ * h * δ⁻¹, hΓ⟩, ?_⟩
    change (δ * h * δ⁻¹) • (δ • τ) = δ • (h • τ)
    rw [← mul_smul, inv_mul_cancel_right, mul_smul]
  have hdist₁ : dist o (δ • (h • τ)) = dist (δ⁻¹ • o) (h • τ) := by
    calc
      dist o (δ • (h • τ)) = dist (δ⁻¹ • o) (δ⁻¹ • (δ • (h • τ))) :=
        (dist_smul δ⁻¹ o (δ • (h • τ))).symm
      _ = _ := by rw [inv_smul_smul]
  have hmove : g • (h • τ) = (γ : G) • τ := by
    rw [← mul_smul, show g * h = (γ : G) from mul_inv_cancel_left g (γ : G)]
  have hdist₂ : dist o (h • τ) = dist (g • o) ((γ : G) • τ) := by
    rw [← hmove, dist_smul]
  have hc : dist o (g • o) ≤ c :=
    Finset.single_le_sum (f := fun a ↦ dist o (a • o)) (fun _ _ ↦ dist_nonneg) hg
  have htriangle : dist (g • o) ((γ : G) • τ) ≤ c + dist o ((γ : G) • τ) := by
    calc
      _ ≤ dist (g • o) o + dist o ((γ : G) • τ) := dist_triangle _ _ _
      _ = dist o (g • o) + dist o ((γ : G) • τ) := by rw [dist_comm (g • o) o]
      _ ≤ _ := add_le_add_left hc _
  apply sub_le_iff_le_add.mpr
  calc
    Metric.infDist o (MulAction.orbit Γ (δ • τ)) ≤ dist o (δ • (h • τ)) :=
      Metric.infDist_le_dist_of_mem hmem
    _ = dist (δ⁻¹ • o) (h • τ) := hdist₁
    _ ≤ dist (δ⁻¹ • o) o + dist o (h • τ) := dist_triangle _ _ _
    _ = dist (δ⁻¹ • o) o + dist (g • o) ((γ : G) • τ) := by rw [hdist₂]
    _ ≤ dist (δ⁻¹ • o) o + (c + dist o ((γ : G) • τ)) := add_le_add_right htriangle _
    _ = dist o ((γ : G) • τ) + (c + dist (δ⁻¹ • o) o) := by ac_rfl

/-- The hyperbolic distance from the base point `o` to the `Γ`-orbit of `τ`. -/
noncomputable def orbitDepth (Γ : Subgroup SL(2, ℝ)) (o τ : ℍ) : ℝ :=
  Metric.infDist o (MulAction.orbit Γ τ)

/-- A commensurator element increases orbit depth by at most an additive constant. -/
theorem exists_orbitDepth_smul_le {Γ : Subgroup SL(2, ℝ)} (o : ℍ)
    {δ : SL(2, ℝ)} (hδ : δ ∈ Subgroup.Commensurable.commensurator Γ) :
    ∃ c : ℝ, ∀ τ : ℍ, orbitDepth Γ o (δ • τ) ≤ orbitDepth Γ o τ + c := by
  obtain ⟨R, hR⟩ := exists_finset_conj_representatives hδ
  exact exists_infDist_orbit_smul_le Γ o δ R hR

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
