import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.Basic

/-!
source-id: JT-SCENE1-CLOSED-NORMAL-QUOTIENT-MAP
source: Joshi III `ss:theta-data-fixing2`; IUT I Definition 3.1(d), geometry-cover
semantics.  This file gives the common-ambient closed-normal subgroup quotient map.
boundary: group quotients only.  It does not define an etale fundamental group,
profinite comparison, or compactness statement.
-/

namespace JoshiTeich.Act1Scene1.ClosedNormalQuotientMap

open scoped Topology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (N : Subgroup G) [N.Normal]
variable {H K : Subgroup G}

/-! The quotient map induced by the inclusion of two subgroups of the same ambient group. -/
noncomputable def map (hHK : H ≤ K) :
    H ⧸ N.subgroupOf H →* K ⧸ N.subgroupOf K :=
  QuotientGroup.quotientMapSubgroupOfOfLe (le_refl N) hHK

/-! A descriptive alias for clients that use the quotient-map terminology. -/
noncomputable def quotientMap (hHK : H ≤ K) :
    H ⧸ N.subgroupOf H →* K ⧸ N.subgroupOf K :=
  map N hHK

@[simp]
theorem map_mk (hHK : H ≤ K) (x : H) :
    map N hHK (QuotientGroup.mk x) =
      QuotientGroup.mk (Subgroup.inclusion hHK x) := by
  rfl

@[simp]
theorem quotientMap_mk (hHK : H ≤ K) (x : H) :
    quotientMap N hHK (QuotientGroup.mk x) =
      QuotientGroup.mk (Subgroup.inclusion hHK x) := by
  rfl

theorem continuous_map (hHK : H ≤ K) :
    Continuous (map N hHK) := by
  apply (QuotientGroup.isQuotientMap_mk (N.subgroupOf H)).continuous_iff.mpr
  have hcomp :
      (map N hHK : H ⧸ N.subgroupOf H → K ⧸ N.subgroupOf K) ∘
          (QuotientGroup.mk : H → H ⧸ N.subgroupOf H) =
        (QuotientGroup.mk : K → K ⧸ N.subgroupOf K) ∘
          (Subgroup.inclusion hHK) := by
    funext q
    simp [map]
  rw [hcomp]
  exact QuotientGroup.continuous_mk.comp (continuous_inclusion hHK)

theorem injective_map (hHK : H ≤ K) :
    Function.Injective (map N hHK) := by
  rw [injective_iff_map_eq_one]
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x hq
  apply (QuotientGroup.eq_one_iff x).2
  have hq' : (QuotientGroup.mk (Subgroup.inclusion hHK x) :
      K ⧸ N.subgroupOf K) = 1 := by
    simpa [map] using hq
  have hxK : (Subgroup.inclusion hHK x : K) ∈ N.subgroupOf K :=
    (QuotientGroup.eq_one_iff (Subgroup.inclusion hHK x)).1 hq'
  exact hxK

theorem isOpenMap_map (hHK : H ≤ K) (hH : IsOpen (H : Set G)) :
    IsOpenMap (map N hHK) := by
  have hqK : IsOpenMap
      (QuotientGroup.mk : K → K ⧸ N.subgroupOf K) :=
    (QuotientGroup.isOpenQuotientMap_mk : IsOpenQuotientMap
      (QuotientGroup.mk : K → K ⧸ N.subgroupOf K)).isOpenMap
  have hi : IsOpenMap (Subgroup.inclusion hHK) := by
    exact hH.isOpenMap_inclusion hHK
  intro U hU
  have hpre : IsOpen ((QuotientGroup.mk : H → H ⧸ N.subgroupOf H) ⁻¹' U) :=
    hU.preimage (QuotientGroup.continuous_mk :
      Continuous (QuotientGroup.mk : H → H ⧸ N.subgroupOf H))
  have hopen : IsOpen ((QuotientGroup.mk : K → K ⧸ N.subgroupOf K) ''
      (Subgroup.inclusion hHK ''
        ((QuotientGroup.mk : H → H ⧸ N.subgroupOf H) ⁻¹' U))) :=
    hqK _ (hi _ hpre)
  have himage :
      map N hHK '' U = (QuotientGroup.mk : K → K ⧸ N.subgroupOf K) ''
        (Subgroup.inclusion hHK ''
          ((QuotientGroup.mk : H → H ⧸ N.subgroupOf H) ⁻¹' U)) := by
    ext z
    constructor
    · rintro ⟨q, hqU, rfl⟩
      revert hqU
      refine QuotientGroup.induction_on q ?_
      intro x
      intro hqU
      have hxU : (QuotientGroup.mk x : H ⧸ N.subgroupOf H) ∈ U := hqU
      exact ⟨Subgroup.inclusion hHK x, ⟨x, hxU, rfl⟩, by simp [map]⟩
    · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨(QuotientGroup.mk y : H ⧸ N.subgroupOf H), hy,
        by simpa [map]⟩
  rw [himage]
  exact hopen

theorem isOpenEmbedding_map (hHK : H ≤ K) (hH : IsOpen (H : Set G)) :
    Topology.IsOpenEmbedding (map N hHK) :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_map N hHK) (injective_map N hHK) (isOpenMap_map N hHK hH)

end JoshiTeich.Act1Scene1.ClosedNormalQuotientMap
