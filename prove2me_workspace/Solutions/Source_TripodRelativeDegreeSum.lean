/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

-/
import Solutions.Source_TripodRelativeDegreeTower

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
