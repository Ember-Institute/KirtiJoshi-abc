/- Private platform body review. Archive modules are inlined with file-local opens
and options scoped to sections. Imported dependencies are listed first. -/

import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.RamificationInertia.Inertia
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Places
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Definitions.Def_TripodCanonicalHighHeightInputs
import Mathlib.Tactic.Tauto

section InertiaDegree

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open NumberField

noncomputable def inertDeg (K : Type*) [Field K] [NumberField K] (w : FinitePlace K) : ℕ :=
  Ideal.inertiaDeg w.maximalIdeal.asIdeal ℤ

end AbcAdaptation.Tripod

end InertiaDegree

section PlaceUnder

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

-/

set_option autoImplicit false

namespace AbcAdaptation.Tripod
open AbcAdaptation.Reference.Iut
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The prime of `𝓞 k` below a finite place of `K`. -/
noncomputable def primeUnder (w : FinitePlace K) : HeightOneSpectrum (𝓞 k) where
  asIdeal := w.maximalIdeal.asIdeal.comap (algebraMap (𝓞 k) (𝓞 K))
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.maximalIdeal.ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)

/-- The finite place of `k` below a finite place of `K`. -/
noncomputable def placeUnder (w : FinitePlace K) : FinitePlace k :=
  FinitePlace.mk (primeUnder w)

lemma placeUnder_maximalIdeal (w : FinitePlace K) :
    (placeUnder (k := k) w).maximalIdeal.asIdeal =
      w.maximalIdeal.asIdeal.comap (algebraMap (𝓞 k) (𝓞 K)) := by
  rw [placeUnder, FinitePlace.maximalIdeal_mk]
  rfl

/-- `w` lies over the place below it. -/
lemma liesOver_placeUnder (w : FinitePlace K) : FinitePlace.LiesOver w (placeUnder (k := k) w) :=
  ⟨by rw [placeUnder_maximalIdeal]⟩

/-- The place below is unique. -/
lemma placeUnder_eq_of_liesOver_place {w : FinitePlace K} {v : FinitePlace k}
    (hwv : FinitePlace.LiesOver w v) : placeUnder w = v := by
  symm
  apply (FinitePlace.maximalIdeal_inj _ _).mp
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [placeUnder_maximalIdeal]
  exact hwv.over

end AbcAdaptation.Tripod

end PlaceUnder

section RelativeValuation

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

-/

set_option autoImplicit false

namespace AbcAdaptation.Tripod
open AbcAdaptation.Reference.Iut
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The ramification index `e(v/w)` of `v` over `w`. -/
noncomputable abbrev relRamIdx (v : FinitePlace K) (w : FinitePlace k) : ℕ :=
  w.maximalIdeal.asIdeal.ramificationIdx' v.maximalIdeal.asIdeal

/-- The residue degree `f(v/w)` of `v` over `w`. -/
noncomputable abbrev relInertDeg (v : FinitePlace K) (w : FinitePlace k) : ℕ :=
  w.maximalIdeal.asIdeal.inertiaDeg' v.maximalIdeal.asIdeal

section Transfer
variable {w : FinitePlace K} {v : FinitePlace k} (hwv : FinitePlace.LiesOver w v)
include hwv

/-- The ramification index of `w` over `v` is nonzero. -/
lemma ramificationIdx'_ne_zero :
    v.maximalIdeal.asIdeal.ramificationIdx' w.maximalIdeal.asIdeal ≠ 0 := by
  haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hwv
  exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _ v.maximalIdeal.ne_bot

/-- `w(x) = v(x)^e` for `x ∈ k`, where `e` is the ramification index of `w` over `v`. -/
lemma valuation_algebraMap_eq_pow (x : k) :
    w.maximalIdeal.valuation K (algebraMap k K x) =
      v.maximalIdeal.valuation k x ^
        v.maximalIdeal.asIdeal.ramificationIdx' w.maximalIdeal.asIdeal := by
  haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hwv
  exact (valuation_liesOver K v.maximalIdeal w.maximalIdeal x).symm

end Transfer

section Nonzero
variable {v : FinitePlace K} {w : FinitePlace k} (hvw : FinitePlace.LiesOver v w)
include hvw

/-- The ramification index `e(v/w)` is nonzero. -/
lemma relRamIdx_ne_zero : relRamIdx v w ≠ 0 := ramificationIdx'_ne_zero hvw

end Nonzero

end AbcAdaptation.Tripod

end RelativeValuation

section FinitePlaceArithmetic

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

-/

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real Classical

noncomputable def ramIdx (K : Type*) [Field K] [NumberField K] (w : FinitePlace K) : ℕ :=
  Ideal.ramificationIdx w.maximalIdeal.asIdeal ℤ

noncomputable def localDeg (K : Type*) [Field K] [NumberField K] (w : FinitePlace K) : ℕ :=
  ramIdx K w * inertDeg K w

noncomputable abbrev completionAt (K : Type*) [Field K] [NumberField K]
    (w : FinitePlace K) := w.maximalIdeal.adicCompletion K

section
variable {k : Type*} [Field k] [NumberField k]
lemma residueChar_prime (w : FinitePlace k) : (AbcAdaptation.Reference.Iut.residueChar w).Prime := by
  haveI : w.maximalIdeal.asIdeal.IsMaximal :=
    w.maximalIdeal.isPrime.isMaximal w.maximalIdeal.ne_bot
  letI : Field (𝓞 k ⧸ w.maximalIdeal.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 k ⧸ w.maximalIdeal.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ w.maximalIdeal.ne_bot
  exact CharP.char_is_prime (𝓞 k ⧸ w.maximalIdeal.asIdeal) (ringChar _)
end

section
variable {K : Type*} [Field K] [NumberField K]
lemma under_int_eq (v : FinitePlace K) :
    v.maximalIdeal.asIdeal.under ℤ = Ideal.span {(AbcAdaptation.Reference.Iut.residueChar v : ℤ)} := by
  set P := v.maximalIdeal.asIdeal
  have hp : (AbcAdaptation.Reference.Iut.residueChar v).Prime := residueChar_prime v
  haveI : CharP (𝓞 K ⧸ P) (AbcAdaptation.Reference.Iut.residueChar v) := ringChar.charP _
  have hmem : (AbcAdaptation.Reference.Iut.residueChar v : ℤ) ∈ P.under ℤ := by
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact Ideal.natCast_mem_of_charP_quotient (AbcAdaptation.Reference.Iut.residueChar v) P
  have hle : Ideal.span {(AbcAdaptation.Reference.Iut.residueChar v : ℤ)} ≤ P.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hmem
  haveI hprime : (Ideal.span {(AbcAdaptation.Reference.Iut.residueChar v : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)
  have hmax : (Ideal.span {(AbcAdaptation.Reference.Iut.residueChar v : ℤ)}).IsMaximal :=
    IsPrime.to_maximal_ideal (by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.ne_zero)
  haveI : (P.under ℤ).IsPrime := Ideal.comap_isPrime _ _
  exact (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm

/-- The prime of `ℤ` below a finite place is nonzero. -/
lemma under_int_ne_bot (v : FinitePlace K) : v.maximalIdeal.asIdeal.under ℤ ≠ ⊥ := by
  rw [under_int_eq, Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast (residueChar_prime v).ne_zero

/-- The prime of `ℤ` below a finite place is maximal. -/
lemma under_int_isMaximal (v : FinitePlace K) : (v.maximalIdeal.asIdeal.under ℤ).IsMaximal := by
  have hp : (AbcAdaptation.Reference.Iut.residueChar v).Prime := residueChar_prime v
  rw [under_int_eq]
  haveI : (Ideal.span {(AbcAdaptation.Reference.Iut.residueChar v : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)
  exact IsPrime.to_maximal_ideal (by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero)

/-- The prime of a finite place lies over `(p)`, `p` its residue characteristic. -/
lemma liesOver_span_residueChar (v : FinitePlace K) :
    v.maximalIdeal.asIdeal.LiesOver (Ideal.span {(AbcAdaptation.Reference.Iut.residueChar v : ℤ)}) :=
  ⟨(under_int_eq v).symm⟩

/-- `N(𝔭_v) = p^{f_v}`. -/
lemma absNorm_eq_pow_residueChar (v : FinitePlace K) :
    Ideal.absNorm v.maximalIdeal.asIdeal = AbcAdaptation.Reference.Iut.residueChar v ^ inertDeg K v := by
  haveI := liesOver_span_residueChar v
  exact (Ideal.pow_inertiaDeg (AbcAdaptation.Reference.Iut.residueChar v) v.maximalIdeal.asIdeal).symm

/-- `f_v > 0`. -/
lemma inertDeg_pos' (v : FinitePlace K) : 0 < inertDeg K v :=
  Ideal.inertiaDeg_pos v.maximalIdeal.asIdeal ℤ

/-- `e_v > 0`. -/
lemma ramIdx_pos' (v : FinitePlace K) : 0 < ramIdx K v :=
  Ideal.ramificationIdx_pos v.maximalIdeal.asIdeal ℤ

/-- The norm of an element of valuation `exp m` is `(p^{f_v})^m`. -/
lemma norm_eq_zpow_of_valued (v : FinitePlace K) (x : completionAt K v) (m : ℤ)
    (hx : Valued.v x = exp m) :
    ‖x‖ = ((AbcAdaptation.Reference.Iut.residueChar v : ℝ) ^ inertDeg K v) ^ m := by
  rw [FinitePlace.norm_def, hx, WithZeroMulInt.toNNReal_neg_apply _ exp_ne_zero]
  have h : (WithZero.unzero (exp_ne_zero (a := m))).toAdd = m := rfl
  rw [h, NNReal.coe_zpow, NNReal.coe_natCast, absNorm_eq_pow_residueChar, Nat.cast_pow]
end

theorem log_apply_eq {T : Type*} [Field T] [NumberField T] (𝔭 : FinitePlace T) {y : T}
    (hy : y ≠ 0) :
    Real.log (𝔭 y) = ((log (𝔭.maximalIdeal.valuation T y) : ℤ) : ℝ) *
      (inertDeg T 𝔭 * Real.log (AbcAdaptation.Reference.Iut.residueChar 𝔭)) := by
  have hv : 𝔭.maximalIdeal.valuation T y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  rw [← FinitePlace.norm_embedding_eq,
    norm_eq_zpow_of_valued 𝔭 _ (log (𝔭.maximalIdeal.valuation T y)) (by
      rw [FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation', exp_log hv]),
    Real.log_zpow, Real.log_pow]

end AbcAdaptation.Tripod

end FinitePlaceArithmetic

section RelativeDegreeTower

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

-/

set_option autoImplicit false

namespace AbcAdaptation.Tripod
open AbcAdaptation.Reference.Iut
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]


section Tower
variable {v : FinitePlace K} {w : FinitePlace k} (hvw : FinitePlace.LiesOver v w)
include hvw

/-- The prime of `ℤ` below `v` is the prime below `w`. -/
lemma under_int_eq_under_int : v.maximalIdeal.asIdeal.under ℤ = w.maximalIdeal.asIdeal.under ℤ := by
  haveI : v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hvw
  rw [← Ideal.under_under (B := 𝓞 k) v.maximalIdeal.asIdeal,
    ← Ideal.over_def v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal]

/-- Places over each other have the same residue characteristic. -/
lemma residueChar_eq_of_liesOver : AbcAdaptation.Reference.Iut.residueChar v = AbcAdaptation.Reference.Iut.residueChar w := by
  have h := under_int_eq_under_int hvw
  rw [under_int_eq, under_int_eq, Ideal.span_singleton_eq_span_singleton] at h
  have h' := Int.natAbs_eq_iff_associated.mpr h
  simpa using h'

/-- `e_v = e_w · e(v/w)`. -/
lemma ramIdx_eq_mul : ramIdx K v = ramIdx k w * relRamIdx v w := by
  haveI : v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hvw
  have hp : v.maximalIdeal.asIdeal.under ℤ ≠ ⊥ := under_int_ne_bot v
  haveI : w.maximalIdeal.asIdeal.LiesOver (v.maximalIdeal.asIdeal.under ℤ) :=
    Ideal.LiesOver.tower_bot v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal _
  have h1 : ramIdx K v = (v.maximalIdeal.asIdeal.under ℤ).ramificationIdx' v.maximalIdeal.asIdeal :=
    (Ideal.ramificationIdx'_eq_ramificationIdx _ v.maximalIdeal.asIdeal hp).symm
  have h2 : ramIdx k w =
      (v.maximalIdeal.asIdeal.under ℤ).ramificationIdx' w.maximalIdeal.asIdeal := by
    have := (Ideal.ramificationIdx'_eq_ramificationIdx (w.maximalIdeal.asIdeal.under ℤ)
      w.maximalIdeal.asIdeal (under_int_ne_bot w)).symm
    rw [under_int_eq_under_int hvw]
    exact this
  rw [h1, h2]
  exact Ideal.ramificationIdx'_algebra_tower' _ w.maximalIdeal.asIdeal v.maximalIdeal.asIdeal

/-- `f_v = f_w · f(v/w)`. -/
lemma inertDeg_eq_mul : inertDeg K v = inertDeg k w * relInertDeg v w := by
  haveI : v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hvw
  haveI : w.maximalIdeal.asIdeal.LiesOver (v.maximalIdeal.asIdeal.under ℤ) :=
    Ideal.LiesOver.tower_bot v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal _
  haveI : (v.maximalIdeal.asIdeal.under ℤ).IsMaximal := under_int_isMaximal v
  haveI : w.maximalIdeal.asIdeal.IsMaximal :=
    w.maximalIdeal.isPrime.isMaximal w.maximalIdeal.ne_bot
  haveI : v.maximalIdeal.asIdeal.IsMaximal :=
    v.maximalIdeal.isPrime.isMaximal v.maximalIdeal.ne_bot
  have h1 : inertDeg K v = (v.maximalIdeal.asIdeal.under ℤ).inertiaDeg' v.maximalIdeal.asIdeal :=
    (Ideal.inertiaDeg'_eq_inertiaDeg _ v.maximalIdeal.asIdeal).symm
  have h2 : inertDeg k w = (v.maximalIdeal.asIdeal.under ℤ).inertiaDeg' w.maximalIdeal.asIdeal := by
    haveI : (w.maximalIdeal.asIdeal.under ℤ).IsMaximal := under_int_isMaximal w
    have := (Ideal.inertiaDeg'_eq_inertiaDeg (w.maximalIdeal.asIdeal.under ℤ)
      w.maximalIdeal.asIdeal).symm
    rw [under_int_eq_under_int hvw]
    exact this
  rw [h1, h2]
  exact Ideal.inertiaDeg'_algebra_tower _ w.maximalIdeal.asIdeal v.maximalIdeal.asIdeal

/-- `[K_v : ℚ_p] = [k_w : ℚ_p] · e(v/w) f(v/w)`. -/
lemma localDeg_eq_mul : localDeg K v = localDeg k w * (relRamIdx v w * relInertDeg v w) := by
  unfold localDeg
  rw [ramIdx_eq_mul hvw, inertDeg_eq_mul hvw]
  ring

end Tower

/-- The local degree `e(w/v) f(w/v)` of `w` over `v`. -/
noncomputable abbrev relLocalDeg (w : FinitePlace K) (v : FinitePlace k) : ℕ :=
  relRamIdx w v * relInertDeg w v

lemma relLocalDeg_ne_zero {w : FinitePlace K} {v : FinitePlace k}
    (hwv : FinitePlace.LiesOver w v) : relLocalDeg w v ≠ 0 := by
  have h := inertDeg_eq_mul hwv
  have hpos := inertDeg_pos' w
  refine mul_ne_zero (relRamIdx_ne_zero hwv) fun h0 => ?_
  rw [h, h0, mul_zero] at hpos
  exact lt_irrefl _ hpos

end AbcAdaptation.Tripod

end RelativeDegreeTower

section FiniteHeightSolution

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

-/

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

end FiniteHeightSolution

section PublishedStatement

set_option autoImplicit false

open AbcAdaptation.Tripod
open AbcAdaptation.Reference.Iut
open NumberField

theorem AbcAdaptation.Tripod.finHeight_algebraMap {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] (y : k) :
    finHeight (algebraMap k K y) = Module.finrank k K * finHeight y :=
  solution (k := k) (K := K) y

end PublishedStatement

#print axioms solution
#print axioms AbcAdaptation.Tripod.under_int_eq_under_int
#print axioms AbcAdaptation.Tripod.residueChar_eq_of_liesOver
#print axioms AbcAdaptation.Tripod.ramIdx_eq_mul
#print axioms AbcAdaptation.Tripod.inertDeg_eq_mul
#print axioms AbcAdaptation.Tripod.localDeg_eq_mul
#print axioms AbcAdaptation.Tripod.relLocalDeg
#print axioms AbcAdaptation.Tripod.relLocalDeg_ne_zero
#print axioms AbcAdaptation.Tripod.sum_localDeg_liesOver
#print axioms AbcAdaptation.Tripod.sum_relLocalDeg_liesOver
#print axioms AbcAdaptation.Tripod.apply_algebraMap_eq_pow
#print axioms AbcAdaptation.Tripod.posLog_apply_algebraMap_eq
#print axioms AbcAdaptation.Tripod.finHeight_algebraMap
