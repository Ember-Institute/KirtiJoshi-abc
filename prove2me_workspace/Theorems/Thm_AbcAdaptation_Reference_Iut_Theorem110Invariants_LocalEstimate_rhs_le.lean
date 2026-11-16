/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
/- Full original rhs_le source proof. Internal source lemmas remain private.
   The complete original LocalEstimate input is retained. -/
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_LogVolumeBound
import Theorems.Thm_AbcAdaptation_Reference_Iut_Theorem110Invariants_LocalEstimate_finsum_le_finsum_of_le
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open scoped BigOperators
open NumberField
open AbcAdaptation.Reference.Iut
open AbcAdaptation.Reference.Iut.Theorem110Invariants
universe u v u₁ u₂

namespace AbcAdaptation.Reference.Iut.HullSystem
variable {C : Type u} {P : DirectSumPresentation.{u, v} C} (H : HullSystem P)
variable {U V : Set P.Total}

/-- The hull of an admissible region belongs to the class of hull regions. -/
private lemma hull_mem_hullRegions (hU : U ∈ H.Admissible) : H.hull U ∈ H.HullRegions :=
  (H.isLeastHullRegion_hull U hU).1

/-- The hull of an admissible region is a hull region `a · O`. -/
private lemma isHullRegion_hull (hU : U ∈ H.Admissible) : P.IsHullRegion (H.hull U) :=
  H.isHullRegion_of_mem _ (H.hull_mem_hullRegions hU)

end AbcAdaptation.Reference.Iut.HullSystem

namespace AbcAdaptation.Reference.Iut.LogVolumeData
open scoped Pointwise
variable {ι : Type u₁} {V : Type u₂}
variable {D : LargeVolumeContainerData.{u₁, u₂, v} ι V} (vol : LogVolumeData D)

/-- The function summed by `globalVol` has finite support: away from the finite
support of the admissible region the packet region is the holomorphic integral region,
whose packet log-volume is `0`. -/
private lemma finite_support_packetVol {i : Fin D.proc.length} (R : D.AdmissibleRegion i) :
    (Function.support fun vQ => vol.packetVol i vQ (R.region vQ)).Finite := by
  refine R.finiteSupport.subset fun vQ hvQ h => ?_
  apply hvQ
  change vol.packetVol i vQ (R.region vQ) = 0
  rw [h]
  exact vol.packetVol_integral i vQ

end AbcAdaptation.Reference.Iut.LogVolumeData

namespace AbcAdaptation.Reference.Iut.Theorem110Invariants.LocalEstimate
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {X : Corollary312VariantData.{u, v} AG TG} (inv : Theorem110Invariants X)
variable (est : inv.LocalEstimate)

-- Restore the local equation simplification context of the published Definitions.
attribute [local simp] dstPlaces.eq_1 placeBound.eq_1 placeBound.eq_2

private lemma support_placeBound_subset (n : ℕ) :
    Function.support (placeBound inv n) ⊆ ↑(insert RationalPlace.infinite (dstPlaces inv)) := by
  intro vQ hvQ
  rcases vQ with p | _
  · have hp : (p : ℕ) ∈ inv.dst := by
      by_contra h
      exact hvQ (by simp [placeBound, h])
    refine Finset.mem_coe.mpr (Finset.mem_insert_of_mem ?_)
    simp only [dstPlaces, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
    exact ⟨p, hp, by rfl⟩
  · exact Finset.mem_coe.mpr (Finset.mem_insert_self _ _)

private lemma infinite_notMem_dstPlaces : RationalPlace.infinite ∉ dstPlaces inv := by
  simp [dstPlaces]

/-- The finite sum of the pointwise bound over all rational places. -/
private lemma finsum_placeBound (n : ℕ) :
    ∑ᶠ vQ, placeBound inv n vQ =
      ∑ p ∈ inv.dst, inv.capsuleBound n p + n * Real.log Real.pi := by
  rw [finsum_eq_sum_of_support_subset _ (support_placeBound_subset inv n),
    Finset.sum_insert (infinite_notMem_dstPlaces inv), add_comm]
  congr 1
  unfold dstPlaces
  rw [Finset.sum_image]
  · rw [← Finset.sum_attach inv.dst fun p => inv.capsuleBound n p]
    refine Finset.sum_congr rfl fun p _ => ?_
    change (if (p.1 : ℕ) ∈ inv.dst then inv.capsuleBound n p.1 else 0) = inv.capsuleBound n p.1
    rw [if_pos p.2]
  · intro p _ q _ h
    exact Subtype.ext (Subtype.mk.inj (RationalPlace.finite.inj h))

variable {inv}
include est

/-- The holomorphic hull of the theta-pilot region is contained in the container of
`est`, by minimality of the hull (taxis #45). -/
private lemma hull_subset_cont (i : Fin X.rhsData.container.proc.length) (vQ : RationalPlace) :
    (X.rhsData.hull.system i vQ).hull ((X.rhsData.thetaPilot i).region vQ) ⊆
      est.cont i vQ :=
  (X.rhsData.hull.system i vQ).hull_le (X.rhsData.thetaPilot_hullAdmissible i vQ)
    (est.cont_mem_hullRegions i vQ) (est.thetaPilot_subset i vQ)

/-- The pointwise bound: the packet log-volume of the hull of the theta-pilot region is
at most `placeBound` at every rational place. -/
private lemma packetVol_hull_le (i : Fin X.rhsData.container.proc.length) (vQ : RationalPlace) :
    X.rhsData.vol.packetVol i vQ ((X.rhsData.thetaHull i).region vQ) ≤
      placeBound inv (X.rhsData.container.proc.capsule i).card vQ := by
  have hmono : X.rhsData.vol.packetVol i vQ ((X.rhsData.thetaHull i).region vQ) ≤
      X.rhsData.vol.packetVol i vQ (est.cont i vQ) :=
    est.packetVol_mono i vQ _ _
      ((X.rhsData.hull.system i vQ).isHullRegion_hull
        (X.rhsData.thetaPilot_hullAdmissible i vQ))
      ((X.rhsData.hull.system i vQ).isHullRegion_of_mem _ (est.cont_mem_hullRegions i vQ))
      (est.hull_subset_cont i vQ)
  refine hmono.trans ?_
  rcases vQ with p | _
  · by_cases hp : (p : ℕ) ∈ inv.dst
    · simpa [placeBound, hp] using est.vol_finite i p hp
    · simp only [placeBound, hp, if_false]
      rw [est.cont_eq_integral i p hp]
      exact (X.rhsData.vol.packetVol_integral i _).le
  · exact est.vol_infinite i

/-- The global log-volume of the hull of the theta-pilot region at capsule `i` is
bounded by the sum of the local bounds. -/
private lemma globalVol_thetaHull_le (i : Fin X.rhsData.container.proc.length) :
    X.rhsData.vol.globalVol (X.rhsData.thetaHull i) ≤
      ∑ p ∈ inv.dst, inv.capsuleBound (X.rhsData.container.proc.capsule i).card p +
        (X.rhsData.container.proc.capsule i).card * Real.log Real.pi := by
  rw [← finsum_placeBound]
  exact finsum_le_finsum_of_le (est.packetVol_hull_le i)
    (X.rhsData.vol.finite_support_packetVol _)
    ((Finset.finite_toSet _).subset (support_placeBound_subset inv _))

end AbcAdaptation.Reference.Iut.Theorem110Invariants.LocalEstimate

open AbcAdaptation.Reference.Iut.Theorem110Invariants.LocalEstimate

theorem AbcAdaptation.Reference.Iut.Theorem110Invariants.LocalEstimate.rhs_le
    {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
    {X : Corollary312VariantData.{u, v} AG TG} {inv : Theorem110Invariants X}
    (est : inv.LocalEstimate) :
    X.rhsData.rhs ≤
      (∑ i, (∑ p ∈ inv.dst, inv.capsuleBound (X.rhsData.container.proc.capsule i).card p +
        (X.rhsData.container.proc.capsule i).card * Real.log Real.pi)) /
        X.rhsData.container.proc.length := by
  unfold RHSData.rhs LogVolumeData.processionVol
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => est.globalVol_thetaHull_le i)
    (Nat.cast_nonneg _)
