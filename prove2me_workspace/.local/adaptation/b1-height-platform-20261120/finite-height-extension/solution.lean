/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

-/
import Definitions.Def_TripodCanonicalHighHeightInputs
import Definitions.Def_AbcAdaptation_Tripod_PlaceUnder
import Definitions.Def_AbcAdaptation_Tripod_RelativeDegreeTower
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

end AbcAdaptation.Tripod

namespace AbcAdaptation.Tripod
open AbcAdaptation.Reference.Iut
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- `∑_{v ∣ w} e_v f_v = [K : k] · e_w f_w`, for any finset `s` of places of `K` consisting of
exactly the places over `w`. -/
theorem sum_localDeg_liesOver (w : FinitePlace k) (s : Finset (FinitePlace K))
    (hs : ∀ v, v ∈ s ↔ FinitePlace.LiesOver v w) :
    ∑ v ∈ s, localDeg K v = Module.finrank k K * localDeg k w := by
  classical
  haveI : w.maximalIdeal.asIdeal.IsMaximal :=
    w.maximalIdeal.isPrime.isMaximal w.maximalIdeal.ne_bot
  have hp0 : w.maximalIdeal.asIdeal ≠ ⊥ := w.maximalIdeal.ne_bot
  have hsum := Ideal.sum_ramification_inertia (𝓞 K) k K hp0 (p := w.maximalIdeal.asIdeal)
  have hbij : ∑ v ∈ s, (relRamIdx v w * relInertDeg v w) =
      ∑ P ∈ IsDedekindDomain.primesOverFinset w.maximalIdeal.asIdeal (𝓞 K),
        w.maximalIdeal.asIdeal.ramificationIdx' P * w.maximalIdeal.asIdeal.inertiaDeg' P := by
    refine Finset.sum_bij (fun v _ => v.maximalIdeal.asIdeal) ?_ ?_ ?_ ?_
    · intro v hv
      haveI : v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := (hs v).mp hv
      exact (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 K)).mpr ⟨inferInstance, inferInstance⟩
    · intro v₁ _ v₂ _ h
      exact (FinitePlace.maximalIdeal_inj _ _).mp (HeightOneSpectrum.ext h)
    · intro P hP
      obtain ⟨hprime, hover⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 K)).mp hP
      have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
      refine ⟨FinitePlace.mk ⟨P, hprime, hne⟩, ?_, ?_⟩
      · rw [hs]
        unfold FinitePlace.LiesOver
        rw [FinitePlace.maximalIdeal_mk]
        exact hover
      · rw [FinitePlace.maximalIdeal_mk]
    · intro v _
      rfl
  have h : ∀ v ∈ s, localDeg K v = localDeg k w * (relRamIdx v w * relInertDeg v w) :=
    fun v hv => localDeg_eq_mul ((hs v).mp hv)
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, hbij, hsum, mul_comm]

/-- `∑_{w ∣ v} e(w/v) f(w/v) = [K : k]`. -/
lemma sum_relLocalDeg_liesOver (v : FinitePlace k) (s : Finset (FinitePlace K))
    (hs : ∀ w, w ∈ s ↔ FinitePlace.LiesOver w v) :
    ∑ w ∈ s, relLocalDeg w v = Module.finrank k K := by
  have h := sum_localDeg_liesOver v s hs
  have h' : ∑ w ∈ s, localDeg K w = localDeg k v * ∑ w ∈ s, relLocalDeg w v := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun w hw => localDeg_eq_mul ((hs w).mp hw)
  have hpos : 0 < localDeg k v := Nat.mul_pos (ramIdx_pos' v) (inertDeg_pos' v)
  rw [h', mul_comm (Module.finrank k K)] at h
  exact Nat.eq_of_mul_eq_mul_left hpos h

end AbcAdaptation.Tripod

namespace AbcAdaptation.Tripod
open AbcAdaptation.Reference.Iut
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- **`|y|_w = |y|_v^{e(w/v) f(w/v)}`** for `y ∈ k` and `w ∣ v`. -/
lemma apply_algebraMap_eq_pow {w : FinitePlace K} {v : FinitePlace k}
    (hwv : FinitePlace.LiesOver w v) (y : k) :
    w (algebraMap k K y) = v y ^ relLocalDeg w v := by
  by_cases hy : y = 0
  · subst hy
    rw [map_zero, map_zero, map_zero, zero_pow (relLocalDeg_ne_zero hwv)]
  have hy' : algebraMap k K y ≠ 0 := (map_ne_zero _).mpr hy
  have hpos : 0 < w (algebraMap k K y) := FinitePlace.pos_iff.mpr hy'
  have hpos' : 0 < v y := FinitePlace.pos_iff.mpr hy
  have hlog : Real.log (w (algebraMap k K y)) = relLocalDeg w v * Real.log (v y) := by
    rw [AbcAdaptation.Tripod.log_apply_eq w hy', AbcAdaptation.Tripod.log_apply_eq v hy,
      valuation_algebraMap_eq_pow hwv, log_pow, inertDeg_eq_mul hwv,
      residueChar_eq_of_liesOver hwv]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  rw [← Real.exp_log hpos, hlog, ← Real.log_pow, Real.exp_log (pow_pos hpos' _)]

/-- `log⁺|y|_w = e(w/v) f(w/v) · log⁺|y|_v` for `y ∈ k` and `w ∣ v`. -/
lemma posLog_apply_algebraMap_eq {w : FinitePlace K} {v : FinitePlace k}
    (hwv : FinitePlace.LiesOver w v) (y : k) :
    log⁺ (w (algebraMap k K y)) = relLocalDeg w v * log⁺ (v y) := by
  rw [apply_algebraMap_eq_pow hwv, Real.posLog_pow]

end AbcAdaptation.Tripod

open AbcAdaptation.Tripod
open AbcAdaptation.Reference.Iut
open NumberField

open scoped Real

theorem solution {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] (y : k) :
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
