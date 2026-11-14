/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Independent uncompiled source-proof draft. Source: Height.lean:84-107,644-653,673-709.
No Iut/Genl import, no provider/Tate/theta package, no new mathematical premise.
-/
import Definitions.Def_TripodLegendreHeightBasics
import Mathlib.Tactic.Tauto

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real Classical

section
variable {T : Type*} [Field T] [NumberField T]
lemma support_posLog_subset (y : T) :
    Function.support (fun v : FinitePlace T => log⁺ (v y)) ⊆
      Function.mulSupport (fun v : FinitePlace T => v y) := by
  intro v hv
  simp only [Function.mem_support, Function.mem_mulSupport] at hv ⊢
  intro h
  apply hv
  rw [h, Real.posLog_one]

/-- `v ↦ log⁺|y|_v` has finite support. -/
lemma hasFiniteSupport_posLog (y : T) :
    Function.HasFiniteSupport (fun v : FinitePlace T => log⁺ (v y)) := by
  by_cases hy : y = 0
  · subst hy
    refine Set.Finite.subset Set.finite_empty ?_
    intro v hv
    simp at hv
  · exact Set.Finite.subset (FinitePlace.hasFiniteMulSupport hy) (support_posLog_subset y)

/-- `h_fin(y)` as a sum over any finite set containing the support. -/
lemma finHeight_eq_sum {y : T} {S : Finset (FinitePlace T)}
    (hS : ∀ v : FinitePlace T, log⁺ (v y) ≠ 0 → v ∈ S) :
    finHeight y = ∑ v ∈ S, log⁺ (v y) :=
  finsum_eq_sum_of_support_subset _ fun v hv => hS v hv


end

variable {K : CompactlyBounded} {x : Pt}

lemma posLog_finite_le (hx : x ∈ K.set) (v : FinitePlace (fieldOf x.1))
    (hv : residueChar v ∈ K.V) :
    log⁺ (v (gen x.1)) ≤ K.c ∧ log⁺ (v (gen x.1)⁻¹) ≤ K.c ∧
      log⁺ (v (gen x.1 - 1)⁻¹) ≤ K.c := by
  obtain ⟨h1, h2⟩ := hx.1 v hv
  refine ⟨(posLog_le_abs_log _).trans h1, ?_, ?_⟩
  · rw [map_inv₀]
    exact (posLog_inv_le_abs_log _).trans h1
  · rw [map_inv₀]
    exact (posLog_inv_le_abs_log _).trans h2

noncomputable def suppFinset (x : Pt) : Finset (FinitePlace (fieldOf x.1)) :=
  (Set.Finite.union
    (Set.Finite.union (hasFiniteSupport_posLog (gen x.1)) (hasFiniteSupport_posLog (gen x.1)⁻¹))
    (Set.Finite.union (hasFiniteSupport_posLog (gen x.1 - 1)⁻¹)
      (hasFiniteSupport_posLog (legendreJ (gen x.1))))).toFinset

lemma mem_suppFinset_of_ne {v : FinitePlace (fieldOf x.1)}
    (h : log⁺ (v (gen x.1)) ≠ 0 ∨ log⁺ (v (gen x.1)⁻¹) ≠ 0 ∨
      log⁺ (v (gen x.1 - 1)⁻¹) ≠ 0 ∨ log⁺ (v (legendreJ (gen x.1))) ≠ 0) :
    v ∈ suppFinset x := by
  rw [suppFinset, Set.Finite.mem_toFinset]
  simp only [Set.mem_union, Function.mem_support]
  tauto

lemma finHeight_gen_eq_sum (x : Pt) :
    finHeight (gen x.1) = ∑ v ∈ suppFinset x, log⁺ (v (gen x.1)) :=
  finHeight_eq_sum fun _ hv => mem_suppFinset_of_ne (Or.inl hv)

lemma finHeight_gen_inv_eq_sum (x : Pt) :
    finHeight (gen x.1)⁻¹ = ∑ v ∈ suppFinset x, log⁺ (v (gen x.1)⁻¹) :=
  finHeight_eq_sum fun _ hv => mem_suppFinset_of_ne (Or.inr (Or.inl hv))

lemma finHeight_gen_sub_one_inv_eq_sum (x : Pt) :
    finHeight (gen x.1 - 1)⁻¹ = ∑ v ∈ suppFinset x, log⁺ (v (gen x.1 - 1)⁻¹) :=
  finHeight_eq_sum fun _ hv => mem_suppFinset_of_ne (Or.inr (Or.inr (Or.inl hv)))

lemma finHeight_legendreJ_eq_sum (x : Pt) :
    finHeight (legendreJ (gen x.1)) = ∑ v ∈ suppFinset x, log⁺ (v (legendreJ (gen x.1))) :=
  finHeight_eq_sum fun _ hv => mem_suppFinset_of_ne (Or.inr (Or.inr (Or.inr hv)))

/-- The sum of the three finite parts as a sum over `suppFinset`. -/
lemma two_mul_finHeight_sum_eq (x : Pt) :
    2 * (finHeight (gen x.1) + finHeight (gen x.1)⁻¹ + finHeight (gen x.1 - 1)⁻¹) =
      ∑ v ∈ suppFinset x,
        2 * (log⁺ (v (gen x.1)) + log⁺ (v (gen x.1)⁻¹) + log⁺ (v (gen x.1 - 1)⁻¹)) := by
  rw [finHeight_gen_eq_sum, finHeight_gen_inv_eq_sum, finHeight_gen_sub_one_inv_eq_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]

end AbcAdaptation.Tripod
