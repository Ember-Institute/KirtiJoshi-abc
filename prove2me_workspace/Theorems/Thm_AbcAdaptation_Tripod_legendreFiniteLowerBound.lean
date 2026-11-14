/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Independent uncompiled source-proof draft. Source: Height.lean:743-784; exact original parent LegendreFiniteLowerBound.
No Iut/Genl import, no provider/Tate/theta package, no new mathematical premise.
-/
import Definitions.Def_TripodLegendreHeightComparisonInputs
import Solutions.Source_TripodFiniteHeightSupport
import Solutions.Source_TripodLegendreFinitePlaceBounds
import Solutions.Source_TripodFinitePrimeCounting
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real Classical

theorem legendreFiniteLowerBound : LegendreFiniteLowerBound := by
  intro K x hx hj
  classical
  have hc := CompactlyBounded.c_nonneg hx
  have hg0 := gen_ne_zero x.2.1
  have hg1 := gen_ne_one x
  rw [two_mul_finHeight_sum_eq, finHeight_legendreJ_eq_sum]
  set S := suppFinset x with hS
  set A : FinitePlace (fieldOf x.1) → ℝ := fun v =>
    2 * (log⁺ (v (gen x.1)) + log⁺ (v (gen x.1)⁻¹) + log⁺ (v (gen x.1 - 1)⁻¹)) with hA
  rw [← Finset.sum_filter_add_sum_filter_not S (fun v => residueChar v ∈ K.V)]
  have hA_le : ∀ v ∈ S.filter (fun v => residueChar v ∈ K.V), A v ≤ 6 * K.c := by
    intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨h1, h2, h3⟩ := posLog_finite_le hx v hv.2
    rw [hA]
    dsimp only
    linarith
  have hA_le' : ∀ v ∈ S.filter (fun v => ¬ residueChar v ∈ K.V),
      A v ≤ log⁺ (v (legendreJ (gen x.1))) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    have h2 : residueChar v ≠ 2 := fun h => hv.2 (h ▸ K.two_mem)
    exact posLog_legendreJ_ge v hg0 hg1 h2 hj
  have hcard := card_filter_residueChar_mem_le x S K.V
  have hcard' : ((S.filter (fun v => residueChar v ∈ K.V)).card : ℝ) ≤ K.V.card * deg x.1 := by
    exact_mod_cast hcard
  calc ∑ v ∈ S.filter (fun v => residueChar v ∈ K.V), A v +
        ∑ v ∈ S.filter (fun v => ¬ residueChar v ∈ K.V), A v
      ≤ ∑ v ∈ S.filter (fun v => residueChar v ∈ K.V), 6 * K.c +
          ∑ v ∈ S.filter (fun v => ¬ residueChar v ∈ K.V), log⁺ (v (legendreJ (gen x.1))) :=
        add_le_add (Finset.sum_le_sum hA_le) (Finset.sum_le_sum hA_le')
    _ = 6 * K.c * (S.filter (fun v => residueChar v ∈ K.V)).card +
          ∑ v ∈ S.filter (fun v => ¬ residueChar v ∈ K.V), log⁺ (v (legendreJ (gen x.1))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ 6 * K.c * (K.V.card * deg x.1) + ∑ v ∈ S, log⁺ (v (legendreJ (gen x.1))) := by
        refine add_le_add (mul_le_mul_of_nonneg_left hcard' (by positivity)) ?_
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => Real.posLog_nonneg
    _ = _ := by ring

end AbcAdaptation.Tripod
