/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Independent uncompiled source-proof draft. Source: TwoAdic.lean:111-181; Height.lean:722-741.
No Iut/Genl import, no provider/Tate/theta package, no new mathematical premise.
-/
import Solutions.Source_TripodFinitePlaceArithmetic

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real Classical

section
variable {K : Type*} [Field K] [NumberField K]
lemma localDeg_eq_ramificationIdx'_mul_inertiaDeg' (w : FinitePlace K) {q : ℕ}
    (hq : residueChar w = q) :
    localDeg K w = (Ideal.span {(q : ℤ)}).ramificationIdx' w.maximalIdeal.asIdeal *
      (Ideal.span {(q : ℤ)}).inertiaDeg' w.maximalIdeal.asIdeal := by
  subst hq
  rw [← under_int_eq]
  haveI : w.maximalIdeal.asIdeal.LiesOver (w.maximalIdeal.asIdeal.under ℤ) := inferInstance
  haveI : (w.maximalIdeal.asIdeal.under ℤ).IsMaximal := under_int_isMaximal w
  haveI : w.maximalIdeal.asIdeal.IsMaximal :=
    w.maximalIdeal.isPrime.isMaximal w.maximalIdeal.ne_bot
  unfold localDeg ramIdx inertDeg
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ w.maximalIdeal.asIdeal (under_int_ne_bot w),
    Ideal.inertiaDeg'_eq_inertiaDeg _ w.maximalIdeal.asIdeal]

/-- `∑_{w ∈ S, p_w = q} [K_w : ℚ_q] ≤ [K : ℚ]` for every finite set `S` of places of `K`
(from `∑_{w ∣ q} e_w f_w = [K : ℚ]`). -/
lemma sum_localDeg_filter_le (S : Finset (FinitePlace K)) (q : ℕ) :
    ∑ w ∈ S.filter (fun w => residueChar w = q), localDeg K w ≤ Module.finrank ℚ K := by
  classical
  by_cases hq : q.Prime
  · set p : Ideal ℤ := Ideal.span {(q : ℤ)} with hp
    haveI hmax : p.IsMaximal := by
      haveI hprime : p.IsPrime :=
        (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).2
          (Nat.prime_iff_prime_int.1 hq)
      exact IsPrime.to_maximal_ideal (by
        rw [hp, ne_eq, Ideal.span_singleton_eq_bot]
        exact_mod_cast hq.ne_zero)
    have hp0 : p ≠ ⊥ := by
      rw [hp, ne_eq, Ideal.span_singleton_eq_bot]
      exact_mod_cast hq.ne_zero
    have hsum := Ideal.sum_ramification_inertia (𝓞 K) ℚ K hp0 (p := p)
    set T := S.filter (fun w => residueChar w = q) with hT
    have hover : ∀ w ∈ T, w.maximalIdeal.asIdeal.LiesOver p := by
      intro w hw
      rw [hT, Finset.mem_filter] at hw
      rw [hp, ← hw.2]
      exact liesOver_span_residueChar w
    have hsub : T.image (fun w : FinitePlace K => w.maximalIdeal.asIdeal) ⊆
        IsDedekindDomain.primesOverFinset p (𝓞 K) := by
      intro P hP
      rw [Finset.mem_image] at hP
      obtain ⟨w, hw, rfl⟩ := hP
      exact (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 K)).mpr
        ⟨inferInstance, hover w hw⟩
    have hinj : Set.InjOn (fun w : FinitePlace K => w.maximalIdeal.asIdeal) T := by
      intro w₁ _ w₂ _ h
      exact FinitePlace.maximalIdeal_injective (HeightOneSpectrum.ext h)
    calc ∑ w ∈ T, localDeg K w
        = ∑ w ∈ T, p.ramificationIdx' w.maximalIdeal.asIdeal *
            p.inertiaDeg' w.maximalIdeal.asIdeal := by
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [hT, Finset.mem_filter] at hw
          exact localDeg_eq_ramificationIdx'_mul_inertiaDeg' w hw.2
      _ = ∑ P ∈ T.image (fun w : FinitePlace K => w.maximalIdeal.asIdeal),
            p.ramificationIdx' P * p.inertiaDeg' P :=
          (Finset.sum_image (f := fun P => p.ramificationIdx' P * p.inertiaDeg' P) hinj).symm
      _ ≤ ∑ P ∈ IsDedekindDomain.primesOverFinset p (𝓞 K),
            p.ramificationIdx' P * p.inertiaDeg' P :=
          Finset.sum_le_sum_of_subset hsub
      _ = Module.finrank ℚ K := hsum
  · refine le_of_eq_of_le (Finset.sum_eq_zero ?_) (Nat.zero_le _)
    intro w hw
    rw [Finset.mem_filter] at hw
    exact absurd (hw.2 ▸ residueChar_prime w) hq

/-- `∑_{w ∈ S, p_w = q} f_w ≤ [K : ℚ]` for every finite set `S` of places of `K`. -/
lemma sum_inertDeg_filter_le (S : Finset (FinitePlace K)) (q : ℕ) :
    ∑ w ∈ S.filter (fun w => residueChar w = q), inertDeg K w ≤ Module.finrank ℚ K := by
  refine le_trans (Finset.sum_le_sum fun w _ => ?_) (sum_localDeg_filter_le S q)
  unfold localDeg
  exact Nat.le_mul_of_pos_left _ (ramIdx_pos' w)
end

lemma card_filter_residueChar_mem_le (x : Pt) (S : Finset (FinitePlace (fieldOf x.1)))
    (V : Finset ℕ) :
    (S.filter (fun v => residueChar v ∈ V)).card ≤ V.card * deg x.1 := by
  classical
  have hsub : S.filter (fun v => residueChar v ∈ V) ⊆
      V.biUnion (fun q => S.filter (fun v => residueChar v = q)) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    rw [Finset.mem_biUnion]
    exact ⟨_, hv.2, Finset.mem_filter.mpr ⟨hv.1, rfl⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  rw [← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun q _ => ?_
  calc (S.filter (fun v => residueChar v = q)).card
      = ∑ v ∈ S.filter (fun v => residueChar v = q), 1 := by rw [Finset.card_eq_sum_ones]
    _ ≤ ∑ v ∈ S.filter (fun v => residueChar v = q), inertDeg (fieldOf x.1) v :=
        Finset.sum_le_sum fun v _ => inertDeg_pos' v
    _ ≤ Module.finrank ℚ (fieldOf x.1) := sum_inertDeg_filter_le S q
    _ = deg x.1 := (deg_eq_finrank x.1).symm

end AbcAdaptation.Tripod
