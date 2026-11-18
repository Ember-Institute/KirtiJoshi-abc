/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

-/
import Solutions.Source_TripodPlaceUnder
import Solutions.Source_TripodRelativeDegreeSum
import Solutions.Source_TripodRelativeAbsoluteValue
import Solutions.Source_TripodFiniteHeightSupport

namespace AbcAdaptation.Tripod
open AbcAdaptation.Reference.Iut
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- **The finite part of the height scales by the extension degree**:
`h_fin^K(y) = [K : k] · h_fin^k(y)` for `y ∈ k`. -/
theorem finHeight_algebraMap (y : k) :
    finHeight (algebraMap k K y) = Module.finrank k K * finHeight y := by
  classical
  have hk : (Function.support fun v : FinitePlace k => log⁺ (v y)).Finite :=
    hasFiniteSupport_posLog y
  have hK : (Function.support fun w : FinitePlace K => log⁺ (w (algebraMap k K y))).Finite :=
    hasFiniteSupport_posLog (algebraMap k K y)
  set Sk := hk.toFinset with hSk
  set SK := hK.toFinset with hSK
  have hmemk : ∀ v, v ∈ Sk ↔ log⁺ (v y) ≠ 0 := fun v => by
    rw [hSk, Set.Finite.mem_toFinset, Function.mem_support]
  have hmemK : ∀ w, w ∈ SK ↔ log⁺ (w (algebraMap k K y)) ≠ 0 := fun w => by
    rw [hSK, Set.Finite.mem_toFinset, Function.mem_support]
  have hfib : ∀ w : FinitePlace K,
      log⁺ (w (algebraMap k K y)) = relLocalDeg w (placeUnder w) * log⁺ (placeUnder w y) :=
    fun w => posLog_apply_algebraMap_eq (liesOver_placeUnder w) y
  have hmaps : ∀ w ∈ SK, placeUnder w ∈ Sk := by
    intro w hw
    rw [hmemK, hfib] at hw
    rw [hmemk]
    exact (mul_ne_zero_iff.mp hw).2
  rw [finHeight_eq_sum fun w hw => (hmemK w).mpr hw, finHeight_eq_sum fun v hv => (hmemk v).mpr hv,
    ← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hs : ∀ w, w ∈ SK.filter (fun w => placeUnder w = v) ↔ FinitePlace.LiesOver w v := by
    intro w
    rw [Finset.mem_filter, hmemK]
    constructor
    · rintro ⟨-, rfl⟩
      exact liesOver_placeUnder w
    · intro hwv
      have hv' := placeUnder_eq_of_liesOver_place hwv
      refine ⟨?_, hv'⟩
      rw [hfib, hv']
      exact mul_ne_zero (by exact_mod_cast relLocalDeg_ne_zero hwv) ((hmemk v).mp hv)
  calc ∑ w ∈ SK.filter (fun w => placeUnder w = v), log⁺ (w (algebraMap k K y))
      = ∑ w ∈ SK.filter (fun w => placeUnder w = v), (relLocalDeg w v : ℝ) * log⁺ (v y) := by
        refine Finset.sum_congr rfl fun w hw => ?_
        rw [posLog_apply_algebraMap_eq ((hs w).mp hw)]
    _ = (Module.finrank k K : ℝ) * log⁺ (v y) := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, sum_relLocalDeg_liesOver v _ hs]

end AbcAdaptation.Tripod
