/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original revision: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviderHeight
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
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FieldTransport
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FieldLegendreFacts
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs

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
lemma residueChar_eq_of_liesOver :
    AbcAdaptation.Reference.Iut.residueChar v = AbcAdaptation.Reference.Iut.residueChar w := by
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

section FinitePlaceMapEquiv

/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Sources: Iut/Cor312/ThetaData/GalCompletion.lean, Iut/Tripod/TwoAdic.lean, and Iut/Tripod/Height.lean.
-/

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero

section IntValuation
variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]

omit [IsDedekindDomain R] [IsDedekindDomain S] in
lemma mem_comap_pow_iff (f : R →+* S) (hf : Function.Bijective f) (I : Ideal S) (a : R)
    (n : ℕ) : a ∈ (I.comap f) ^ n ↔ f a ∈ I ^ n := by
  let e := RingEquiv.ofBijective f hf
  have he : I.comap f = I.comap e := by
    ext x; rw [Ideal.mem_comap, Ideal.mem_comap, RingEquiv.coe_ofBijective]
  have hea : f a = e a := (RingEquiv.coe_ofBijective f hf).symm ▸ rfl
  rw [he, hea, ← Ideal.map_symm, ← Ideal.map_pow, Ideal.map_symm, Ideal.mem_comap]

/-- The `intValuation` at the prime `w = f⁻¹(v)` of `a` is the `intValuation` at `v` of `f a`. -/
theorem intValuation_of_comap {v : HeightOneSpectrum S} {w : HeightOneSpectrum R} (f : R →+* S)
    (hf : Function.Bijective f) (hw : w.asIdeal = v.asIdeal.comap f) (a : R) :
    w.intValuation a = v.intValuation (f a) := by
  have key : ∀ n : ℕ, w.intValuation a ≤ exp (-(n : ℤ)) ↔
      v.intValuation (f a) ≤ exp (-(n : ℤ)) := by
    intro n
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem,
      hw]
    exact mem_comap_pow_iff f hf v.asIdeal a n
  by_cases ha : a = 0
  · subst ha; simp
  have hfa : f a ≠ 0 := (map_ne_zero_iff f hf.injective).2 ha
  obtain ⟨m, hm⟩ : ∃ m : ℕ, w.intValuation a = exp (-(m : ℤ)) :=
    ⟨_, w.intValuation_if_neg ha⟩
  obtain ⟨m', hm'⟩ : ∃ m' : ℕ, v.intValuation (f a) = exp (-(m' : ℤ)) :=
    ⟨_, v.intValuation_if_neg hfa⟩
  rw [hm, hm'] at key ⊢
  simp only [exp_le_exp, neg_le_neg_iff, Nat.cast_le] at key
  rw [le_antisymm ((key m).1 le_rfl) ((key m').2 le_rfl)]

/-- The valuation at `w = f⁻¹(v)` of `x` is the valuation at `v` of `φ x`, for `φ` a field
homomorphism extending `f`. -/
theorem valuation_of_comap {K L : Type*} [Field K] [Algebra R K] [IsFractionRing R K] [Field L]
    [Algebra S L] [IsFractionRing S L] {v : HeightOneSpectrum S} {w : HeightOneSpectrum R}
    (f : R →+* S) (hf : Function.Bijective f) (hw : w.asIdeal = v.asIdeal.comap f)
    (φ : K →+* L) (hφ : ∀ r : R, φ (algebraMap R K r) = algebraMap S L (f r)) (x : K) :
    w.valuation K x = v.valuation L (φ x) := by
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
  have h3 : v.valuation L (algebraMap S L (f r)) = v.intValuation (f r) :=
    v.valuation_of_algebraMap (K := L) (f r)
  have h4 : v.valuation L (algebraMap S L (f s)) = v.intValuation (f s) :=
    v.valuation_of_algebraMap (K := L) (f s)
  change w.valuation K (IsLocalization.mk' K r s) = v.valuation L (φ (IsLocalization.mk' K r s))
  rw [HeightOneSpectrum.valuation_of_mk', IsFractionRing.mk'_eq_div, map_div₀, hφ, hφ, map_div₀,
    h3, h4, intValuation_of_comap f hf hw, intValuation_of_comap f hf hw]

end IntValuation

lemma toNNReal_congr {e e' : NNReal} (h : e = e') (he : e ≠ 0) (he' : e' ≠ 0) (x : ℤᵐ⁰) :
    WithZeroMulInt.toNNReal he x = WithZeroMulInt.toNNReal he' x := by
  subst h; rfl

section MapEquiv
variable {k k' : Type*} [Field k] [NumberField k] [Field k'] [NumberField k']

/-- **The bijection of finite places along an isomorphism** `e : k ≃+* k'` of number fields:
the place of the prime `(e⁻¹)⁻¹(𝔭_v) = e(𝔭_v)` of `𝓞 k'`. -/
noncomputable def FinitePlace.mapEquiv (e : k ≃+* k') : FinitePlace k ≃ FinitePlace k' :=
  FinitePlace.equivHeightOneSpectrum.trans
    ((HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)).trans
      FinitePlace.equivHeightOneSpectrum.symm)

variable (e : k ≃+* k') (v : FinitePlace k)

lemma FinitePlace.mapEquiv_maximalIdeal :
    (FinitePlace.mapEquiv e v).maximalIdeal.asIdeal =
      v.maximalIdeal.asIdeal.comap ((RingOfIntegers.mapRingEquiv e).symm : 𝓞 k' →+* 𝓞 k) := by
  simp only [FinitePlace.mapEquiv, Equiv.trans_apply, FinitePlace.equivHeightOneSpectrum_apply,
    HeightOneSpectrum.equivOfRingEquiv_apply]
  exact congrArg HeightOneSpectrum.asIdeal (FinitePlace.maximalIdeal_mk _)

/-- The valuation of the transported place is the valuation of `e⁻¹`. -/
lemma FinitePlace.mapEquiv_valuation (x : k') :
    (FinitePlace.mapEquiv e v).maximalIdeal.valuation k' x =
      v.maximalIdeal.valuation k (e.symm x) :=
  valuation_of_comap ((RingOfIntegers.mapRingEquiv e).symm : 𝓞 k' →+* 𝓞 k)
    (RingOfIntegers.mapRingEquiv e).symm.bijective (FinitePlace.mapEquiv_maximalIdeal e v)
    (e.symm : k' →+* k) (fun _ => rfl) x

/-- The absolute norm of the prime of the transported place. -/
lemma FinitePlace.mapEquiv_absNorm :
    Ideal.absNorm (FinitePlace.mapEquiv e v).maximalIdeal.asIdeal =
      Ideal.absNorm v.maximalIdeal.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  have hIJ : v.maximalIdeal.asIdeal =
      (FinitePlace.mapEquiv e v).maximalIdeal.asIdeal.map
        ((RingOfIntegers.mapRingEquiv e).symm : 𝓞 k' →+* 𝓞 k) := by
    rw [FinitePlace.mapEquiv_maximalIdeal,
      Ideal.map_comap_of_surjective (f := ((RingOfIntegers.mapRingEquiv e).symm : 𝓞 k' →+* 𝓞 k))
        (RingOfIntegers.mapRingEquiv e).symm.surjective]
  exact Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv e).symm hIJ).toEquiv

/-- The absolute value of the transported place is the absolute value of `e⁻¹`. -/
lemma FinitePlace.mapEquiv_apply (x : k') :
    FinitePlace.mapEquiv e v x = v (e.symm x) := by
  rw [← FinitePlace.norm_embedding_eq, ← FinitePlace.norm_embedding_eq,
    FinitePlace.norm_embedding', FinitePlace.norm_embedding', FinitePlace.mapEquiv_valuation]
  congr 1
  refine toNNReal_congr ?_ _ _ _
  exact_mod_cast FinitePlace.mapEquiv_absNorm e v

end MapEquiv
end AbcAdaptation.Reference.Iut

end FinitePlaceMapEquiv

section TwoAdicHypothesis

namespace AbcAdaptation.Reference.Iut.LocalHeightData

open Finset Real

variable (L : LocalHeightData)

/-- The part of `log(q_∀)` supported at the places of residue characteristic `q`. -/
noncomputable def heightEq (q : ℕ) : ℝ :=
  (∑ v ∈ L.bad.filter (fun v => L.p v = q), (L.hv v : ℝ) * L.f v * Real.log (L.p v)) / L.deg

end AbcAdaptation.Reference.Iut.LocalHeightData

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum WithZero WeierstrassCurve
open scoped WithZero Real Classical

variable (P : CurveProviders) (K : CompactlyBounded)

def TwoAdicBoundHyp (B : ℝ) : Prop := ∀ x ∈ K.set, (P.localData x).heightEq 2 ≤ B

end AbcAdaptation.Tripod

end TwoAdicHypothesis

section FinitePlaceResidueTransport

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

section
variable {k : Type*} [Field k] [NumberField k]

lemma natCast_mem_maximalIdeal_iff (v : FinitePlace k) {q : ℕ} (hq : q.Prime) :
    (q : 𝓞 k) ∈ v.maximalIdeal.asIdeal ↔ AbcAdaptation.Reference.Iut.residueChar v = q := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast,
    CharP.cast_eq_zero_iff (𝓞 k ⧸ v.maximalIdeal.asIdeal) (ringChar _)]
  exact Nat.prime_dvd_prime_iff_eq (residueChar_prime v) hq
end

section
variable {k k' : Type*} [Field k] [NumberField k] [Field k'] [NumberField k']
variable (e : k ≃+* k') (v : FinitePlace k)

lemma FinitePlace.mapEquiv_residueChar :
    AbcAdaptation.Reference.Iut.residueChar (FinitePlace.mapEquiv e v) = AbcAdaptation.Reference.Iut.residueChar v := by
  rw [← natCast_mem_maximalIdeal_iff _ (residueChar_prime v), FinitePlace.mapEquiv_maximalIdeal,
    Ideal.mem_comap, map_natCast]
  exact (natCast_mem_maximalIdeal_iff v (residueChar_prime v)).mpr rfl

end

end AbcAdaptation.Reference.Iut

end FinitePlaceResidueTransport

section TripodalPlaceTransport

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum WithZero WeierstrassCurve
open scoped WithZero Real Classical

variable (P : CurveProviders) (x : Pt)

theorem genT_ne_zero : genT P x ≠ 0 := fun h => gen'_ne_zero x.2.1 (congrArg Subtype.val h)

theorem genT_sub_one_ne_zero : genT P x - 1 ≠ 0 := by
  intro h
  exact gen'_ne_one x.2.2 (congrArg Subtype.val (sub_eq_zero.mp h))

theorem tpdEquiv_symm_gen : (tpdEquiv P x).symm (gen x.1) = genT P x := by
  rw [← tpdEquiv_genT, AlgEquiv.symm_apply_apply]

noncomputable abbrev tpdPlace (𝔭 : FinitePlace (tpd P x)) : FinitePlace (fieldOf x.1) :=
  FinitePlace.mapEquiv (tpdEquiv P x : tpd P x ≃+* fieldOf x.1) 𝔭

theorem tpdPlace_gen (𝔭 : FinitePlace (tpd P x)) : tpdPlace P x 𝔭 (gen x.1) = 𝔭 (genT P x) := by
  rw [tpdPlace, FinitePlace.mapEquiv_apply]
  congr 1
  exact tpdEquiv_symm_gen P x

theorem tpdPlace_gen_sub_one (𝔭 : FinitePlace (tpd P x)) :
    tpdPlace P x 𝔭 (gen x.1 - 1) = 𝔭 (genT P x - 1) := by
  rw [tpdPlace, FinitePlace.mapEquiv_apply, map_sub, map_one]
  congr 2
  exact tpdEquiv_symm_gen P x

theorem residueChar_tpdPlace (𝔭 : FinitePlace (tpd P x)) :
    AbcAdaptation.Reference.Iut.residueChar (tpdPlace P x 𝔭) = AbcAdaptation.Reference.Iut.residueChar 𝔭 :=
  FinitePlace.mapEquiv_residueChar _ _

end AbcAdaptation.Tripod

end TripodalPlaceTransport

section TripodalCompactValuation

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum WithZero WeierstrassCurve
open scoped WithZero Real Classical

lemma log_natCast_nonneg (p : ℕ) : 0 ≤ Real.log p := by
  rcases Nat.eq_zero_or_pos p with h | h
  · simp [h]
  · exact Real.log_nonneg (by exact_mod_cast h)

variable (P : CurveProviders) (x : Pt)

theorem abs_log_valuation_mul_le {K : CompactlyBounded} (hx : x ∈ K.set)
    (𝔭 : FinitePlace (tpd P x)) (h𝔭 : AbcAdaptation.Reference.Iut.residueChar 𝔭 ∈ K.V) :
    |((log (𝔭.maximalIdeal.valuation _ (genT P x)) : ℤ) : ℝ)| *
        (inertDeg (tpd P x) 𝔭 * Real.log (AbcAdaptation.Reference.Iut.residueChar 𝔭)) ≤ K.c ∧
      |((log (𝔭.maximalIdeal.valuation _ (genT P x - 1)) : ℤ) : ℝ)| *
        (inertDeg (tpd P x) 𝔭 * Real.log (AbcAdaptation.Reference.Iut.residueChar 𝔭)) ≤ K.c := by
  have hmem : AbcAdaptation.Reference.Iut.residueChar (tpdPlace P x 𝔭) ∈ K.V :=
    (residueChar_tpdPlace P x 𝔭).symm ▸ h𝔭
  have hb := hx.1 (tpdPlace P x 𝔭) hmem
  rw [tpdPlace_gen, tpdPlace_gen_sub_one, log_apply_eq _ (genT_ne_zero P x),
    log_apply_eq _ (genT_sub_one_ne_zero P x)] at hb
  have hpos : 0 ≤ (inertDeg (tpd P x) 𝔭 : ℝ) * Real.log (AbcAdaptation.Reference.Iut.residueChar 𝔭) :=
    mul_nonneg (Nat.cast_nonneg _) (log_natCast_nonneg _)
  obtain ⟨h1, h2⟩ := hb
  rw [abs_mul, abs_of_nonneg hpos] at h1 h2
  exact ⟨h1, h2⟩

end AbcAdaptation.Tripod

end TripodalCompactValuation

section TwoAdicLegendreValuation

namespace AbcAdaptation.Tripod

open WithZero WeierstrassCurve
open scoped WithZero

section
variable {K : Type*} [Field K] [NeZero (2 : K)] (v : Valuation K ℤᵐ⁰) {l : K}
  [(legendre l).IsElliptic]

lemma valuation_legendre_ne_zero (hj : v (legendre l).j ≠ 0) :
    v 256 ≠ 0 ∧ v (l ^ 2 - l + 1) ≠ 0 ∧ v l ≠ 0 ∧ v (l - 1) ≠ 0 := by
  have hl0 : l ≠ 0 := ne_zero_of_legendre_isElliptic
  have hl1 : l - 1 ≠ 0 := sub_ne_zero.mpr ne_one_of_legendre_isElliptic
  rw [legendre_j, map_div₀, map_mul, map_pow] at hj
  have hnum := (div_ne_zero_iff.mp hj).1
  exact ⟨(mul_ne_zero_iff.mp hnum).1,
    (pow_ne_zero_iff (by norm_num)).mp (mul_ne_zero_iff.mp hnum).2,
    (Valuation.ne_zero_iff v).mpr hl0, (Valuation.ne_zero_iff v).mpr hl1⟩

/-- `log v(j) = log v(256) + 3 log v(λ² − λ + 1) − 2 log v(λ) − 2 log v(λ − 1)`. -/
lemma log_valuation_legendre_j (hj : v (legendre l).j ≠ 0) :
    log (v (legendre l).j) = log (v 256) + 3 * log (v (l ^ 2 - l + 1)) -
      (2 * log (v l) + 2 * log (v (l - 1))) := by
  obtain ⟨h256, hc, hvl, hvl1⟩ := valuation_legendre_ne_zero v hj
  rw [legendre_j, map_div₀, map_mul, map_pow, map_mul, map_pow, map_pow,
    log_div (mul_ne_zero h256 (pow_ne_zero _ hc))
      (mul_ne_zero (pow_ne_zero _ hvl) (pow_ne_zero _ hvl1)),
    log_mul h256 (pow_ne_zero _ hc), log_pow, log_mul (pow_ne_zero _ hvl) (pow_ne_zero _ hvl1),
    log_pow, log_pow]
  simp only [nsmul_eq_mul]
  push_cast
  ring

omit [NeZero (2 : K)] [(legendre l).IsElliptic] in
/-- `log v(λ² − λ + 1) ≤ log v(λ) + log v(λ − 1)` or `≤ 0` (ultrametric inequality for
`λ² − λ + 1 = λ(λ − 1) + 1`). -/
lemma log_valuation_sq_sub_add_one_le (hc : v (l ^ 2 - l + 1) ≠ 0) (hl : v l ≠ 0)
    (hl1 : v (l - 1) ≠ 0) :
    log (v (l ^ 2 - l + 1)) ≤ log (v l) + log (v (l - 1)) ∨ log (v (l ^ 2 - l + 1)) ≤ 0 := by
  have h : l ^ 2 - l + 1 = l * (l - 1) + 1 := by ring
  rw [h] at hc ⊢
  rcases Valuation.map_add' v (l * (l - 1)) 1 with h1 | h1
  · left
    rw [map_mul] at h1
    rw [← log_mul hl hl1]
    exact (log_le_log hc (mul_ne_zero hl hl1)).mpr h1
  · right
    rw [map_one] at h1
    have := (log_le_log hc one_ne_zero).mpr h1
    simpa using this

/-- **The bound on `log v(j(E_λ))`**: if `v(256) ≤ 1` then
`log v(j) ≤ 2|log v(λ)| + 2|log v(λ − 1)|`. -/
lemma log_valuation_legendre_j_le (h256 : v 256 ≤ 1) (hj : v (legendre l).j ≠ 0) :
    log (v (legendre l).j) ≤ 2 * |log (v l)| + 2 * |log (v (l - 1))| := by
  obtain ⟨h256', hc, hvl, hvl1⟩ := valuation_legendre_ne_zero v hj
  have hd : log (v 256) ≤ 0 := by
    have := (log_le_log h256' one_ne_zero).mpr h256
    simpa using this
  rw [log_valuation_legendre_j v hj]
  have ha := le_abs_self (log (v l))
  have ha' := neg_abs_le (log (v l))
  have hb := le_abs_self (log (v (l - 1)))
  have hb' := neg_abs_le (log (v (l - 1)))
  have ha0 := abs_nonneg (log (v l))
  have hb0 := abs_nonneg (log (v (l - 1)))
  rcases log_valuation_sq_sub_add_one_le v hc hvl hvl1 with h | h
  · linarith
  · linarith

end

end AbcAdaptation.Tripod

end TwoAdicLegendreValuation

section TatePoleOrder

namespace AbcAdaptation.Reference.TateCurvesTheta.TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- The norm of the Tate curve's `j`-invariant is the inverse norm of its parameter. -/
theorem norm_tateJ (t : TateParameter K) (h12 : (12 : K) ≠ 0) :
    ‖t.tateJ‖ = ‖(t.q : K)‖⁻¹ := by
  rw [tateJ, norm_div, norm_pow, t.norm_tateCurve_c₄, one_pow, t.norm_tateCurve_Δ h12,
    one_div]

omit [CompleteSpace K] [IsUltrametricDist K] in
lemma norm_q_eq_pow_orderNat (t : TateParameter K) {π : K} (hπ : IsUniformizer π) :
    ‖(t.q : K)‖ = ‖π‖ ^ (t.toOrdered hπ).orderNat := by
  have hpos := t.orderZ_pos hπ
  rw [show (t.toOrdered hπ).orderNat = (t.orderZ hπ).toNat from rfl,
    ← zpow_natCast, Int.toNat_of_nonneg hpos.le]
  exact t.norm_q_eq_zpow hπ

end AbcAdaptation.Reference.TateCurvesTheta.TateParameter

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum TateCurvesTheta WithZero
open scoped WithZero

section
variable {k : Type*} [Field k] [NumberField k] (w : FinitePlace k)

lemma valued_eq_of_isUniformizer {π : localCompletion w} (hπ : IsUniformizer π) :
    Valued.v π = exp (-1 : ℤ) := by
  obtain ⟨π₀, hπ₀⟩ := w.maximalIdeal.valuation_exists_uniformizer k
  have hπ₀' : Valued.v (FinitePlace.embedding w.maximalIdeal π₀ : localCompletion w) =
      exp (-1 : ℤ) := by
    rw [FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation', hπ₀]
  have hN : (1 : ℝ) < (AbcAdaptation.Reference.Iut.residueChar w : ℝ) ^ Tripod.inertDeg k w := by
    have hp := Tripod.residueChar_prime w
    exact one_lt_pow₀ (by exact_mod_cast hp.one_lt) (Tripod.inertDeg_pos' w).ne'
  have hN0 : (0 : ℝ) < (AbcAdaptation.Reference.Iut.residueChar w : ℝ) ^ Tripod.inertDeg k w := zero_lt_one.trans hN
  have hπ' : Valued.v π ≠ 0 := (Valuation.ne_zero_iff _).2 hπ.ne_zero
  set m : ℤ := log (Valued.v π)
  have hm : Valued.v π = exp m := (exp_log hπ').symm
  have hnorm := Tripod.norm_eq_zpow_of_valued w π m hm
  have hm0 : m < 0 := by
    have h := hπ.norm_lt_one
    rw [hnorm, zpow_lt_one_iff_right₀ hN] at h
    exact h
  have hunit : (FinitePlace.embedding w.maximalIdeal π₀ : localCompletion w) ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ₀'
    exact exp_ne_zero hπ₀'.symm
  obtain ⟨n, hn⟩ := hπ.generates (Units.mk0 _ hunit)
  rw [Units.val_mk0, Tripod.norm_eq_zpow_of_valued w _ _ hπ₀', hnorm, ← zpow_mul] at hn
  have hmn : (-1 : ℤ) = m * n := zpow_right_injective₀ hN0 hN.ne' hn
  have hm1 : m = -1 := by
    have hunit : IsUnit m := IsUnit.of_mul_eq_one (-n) (by rw [mul_neg, ← hmn]; norm_num)
    rcases Int.isUnit_iff.mp hunit with h | h
    · omega
    · exact h
  rw [hm, hm1]

variable {w}

/-- The valuation exponent of a Tate parameter is its negative normalized order. -/
lemma valued_tateParameter_q (t : TateParameter (localCompletion w)) {π : localCompletion w}
    (hπ : IsUniformizer π) :
    Valued.v (t.q : localCompletion w) = exp (-((t.toOrdered hπ).orderNat : ℤ)) := by
  have hq : (t.q : localCompletion w) ≠ 0 := t.q.ne_zero
  have hq' : Valued.v (t.q : localCompletion w) ≠ 0 := (Valuation.ne_zero_iff _).2 hq
  set m : ℤ := log (Valued.v (t.q : localCompletion w))
  have hm : Valued.v (t.q : localCompletion w) = exp m := (exp_log hq').symm
  have hN : (1 : ℝ) < (AbcAdaptation.Reference.Iut.residueChar w : ℝ) ^ Tripod.inertDeg k w := by
    have hp := Tripod.residueChar_prime w
    exact one_lt_pow₀ (by exact_mod_cast hp.one_lt) (Tripod.inertDeg_pos' w).ne'
  have h1 := t.norm_q_eq_pow_orderNat hπ
  rw [Tripod.norm_eq_zpow_of_valued w _ m hm,
    Tripod.norm_eq_zpow_of_valued w π _ (valued_eq_of_isUniformizer w hπ)] at h1
  let N : ℝ := (AbcAdaptation.Reference.Iut.residueChar w : ℝ) ^ Tripod.inertDeg k w
  have heq : N ^ m = N ^ ((-1 : ℤ) * ((t.toOrdered hπ).orderNat : ℤ)) := by
    calc
      N ^ m = (N ^ (-1 : ℤ)) ^ (t.toOrdered hπ).orderNat := h1
      _ = _ := by rw [zpow_mul, zpow_natCast]
  have he := zpow_right_injective₀ (zero_lt_one.trans hN) hN.ne' heq
  rw [hm, he, neg_one_mul]
end

namespace EllipticCurveData

variable (C : EllipticCurveData) {w : FinitePlace C.F}

/-- At a multiplicative place, the order of the Tate parameter is the pole order of `j`. -/
lemma valuation_j_eq_exp_qOrder (hw : w ∈ C.badAll) :
    w.maximalIdeal.valuation C.F C.E.j = exp ((C.tateInputs.qOrder w hw : ℕ) : ℤ) := by
  have hq : Valued.v ((C.tateInputs.tate w hw).q : localCompletion w) =
      exp (-((C.tateInputs.qOrder w hw : ℕ) : ℤ)) :=
    valued_tateParameter_q _ (C.tateInputs.unif_isUniformizer w hw)
  have hJ : (C.tateInputs.tate w hw).tateJ = FinitePlace.embedding w.maximalIdeal C.E.j :=
    C.tateInputs.tateJ_eq w hw
  have hnorm : ‖(C.tateInputs.tate w hw).tateJ‖ =
      ‖((C.tateInputs.tate w hw).q : localCompletion w)‖⁻¹ :=
    (C.tateInputs.tate w hw).norm_tateJ (twelve_ne_zero w)
  have hq0 : ((C.tateInputs.tate w hw).q : localCompletion w) ≠ 0 :=
    (C.tateInputs.tate w hw).q.ne_zero
  have h1 : ‖(C.tateInputs.tate w hw).tateJ * ((C.tateInputs.tate w hw).q : localCompletion w)‖
      = 1 := by
    rw [norm_mul, hnorm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hq0)]
  rw [norm_eq_one_iff_valued, map_mul, hJ, hq, FinitePlace.embedding_apply,
    valuedAdicCompletion_eq_valuation', exp_neg] at h1
  rw [eq_inv_of_mul_eq_one_left h1, inv_inv]

end EllipticCurveData
end AbcAdaptation.Reference.Iut

end TatePoleOrder

section CompactBound

namespace AbcAdaptation.Tripod

open NumberField

theorem CompactlyBounded.c_nonneg {K : CompactlyBounded} {x : Pt}
    (hx : x ∈ K.set) : 0 ≤ K.c := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace (fieldOf x.1)) := inferInstance
  exact (abs_nonneg _).trans (hx.2 w).1

end AbcAdaptation.Tripod

end CompactBound

section LocalDegrees

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real Classical

theorem valuation_256_le_one {T : Type*} [Field T] [NumberField T] (w : FinitePlace T) :
    w.maximalIdeal.valuation T 256 ≤ 1 := by
  have : (256 : T) = algebraMap (𝓞 T) T 256 := by rw [map_ofNat]
  rw [this]
  exact valuation_le_one _ _

section
variable {K : Type*} [Field K] [NumberField K]
lemma localDeg_eq_ramificationIdx'_mul_inertiaDeg' (w : FinitePlace K) {q : ℕ}
    (hq : AbcAdaptation.Reference.Iut.residueChar w = q) :
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
    ∑ w ∈ S.filter (fun w => AbcAdaptation.Reference.Iut.residueChar w = q), localDeg K w ≤ Module.finrank ℚ K := by
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
    set T := S.filter (fun w => AbcAdaptation.Reference.Iut.residueChar w = q) with hT
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

end

end AbcAdaptation.Tripod

end LocalDegrees

section TwoAdicLocalTerm

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum WithZero WeierstrassCurve
open scoped WithZero Real Classical

variable (P : CurveProviders) (x : Pt)

lemma term_le_aux {N A B E Fr Fp L D c : ℝ} (hN : N ≤ 2 * E * (A + B))
    (hA : A * (Fp * L) ≤ c) (hB : B * (Fp * L) ≤ c) (hE : 0 ≤ E) (hFr : 0 ≤ Fr) (hFp : 0 ≤ Fp)
    (hL : 0 ≤ L) (hD : 1 ≤ D) (hc : 0 ≤ c) :
    N * (Fp * Fr) * L ≤ 4 * c * (D * (E * Fr)) := by
  calc N * (Fp * Fr) * L = N * (Fr * (Fp * L)) := by ring
    _ ≤ 2 * E * (A + B) * (Fr * (Fp * L)) :=
        mul_le_mul_of_nonneg_right hN (by positivity)
    _ = 2 * E * Fr * (A * (Fp * L) + B * (Fp * L)) := by ring
    _ ≤ 2 * E * Fr * (c + c) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hB) (by positivity)
    _ = 4 * c * (1 * (E * Fr)) := by ring
    _ ≤ 4 * c * (D * (E * Fr)) := by gcongr

/-- **The local bound at a place over `2`**: for `w ∣ 𝔭` with `w` multiplicative and
`p_𝔭 = 2 ∈ V`, `h_w f_w log 2 ≤ 4c·[F_w : ℚ_2]`. -/
theorem term_le {K : CompactlyBounded} (hx : x ∈ K.set) {w : FinitePlace (P.curve x).F}
    (hw : w ∈ (P.curve x).badAll) (hw2 : AbcAdaptation.Reference.Iut.residueChar w = 2) :
    ((P.tate x).qOrder w hw : ℝ) * inertDeg (P.curve x).F w * Real.log (AbcAdaptation.Reference.Iut.residueChar w) ≤
      4 * K.c * localDeg (P.curve x).F w := by
  set 𝔭 : FinitePlace (tpd P x) := placeUnder w with h𝔭
  have hw𝔭 : FinitePlace.LiesOver w 𝔭 := liesOver_placeUnder w
  have h𝔭2 : AbcAdaptation.Reference.Iut.residueChar 𝔭 = 2 :=
    (residueChar_eq_of_liesOver hw𝔭).symm.trans hw2
  have hc := CompactlyBounded.c_nonneg hx
  -- the order of the Tate parameter is `log v_w(j)`
  have hvj := (P.curve x).valuation_j_eq_exp_qOrder hw
  have hj0 : w.maximalIdeal.valuation _ (P.curve x).E.j ≠ 0 := by rw [hvj]; exact exp_ne_zero
  have hn : ((P.tate x).qOrder w hw : ℤ) ≤
      2 * |log (w.maximalIdeal.valuation _ (genC' P x))| +
        2 * |log (w.maximalIdeal.valuation _ (genC' P x - 1))| := by
    have this : log (w.maximalIdeal.valuation _ (P.curve x).E.j) ≤
        2 * |log (w.maximalIdeal.valuation _ (genC' P x))| +
          2 * |log (w.maximalIdeal.valuation _ (genC' P x - 1))| :=
      log_valuation_legendre_j_le (w.maximalIdeal.valuation (P.curve x).F)
        (l := genC' P x) (valuation_256_le_one w) hj0
    rwa [hvj, log_exp] at this
  -- the valuations at `w` are the `e(w/𝔭)`-th powers of those at `𝔭`
  set e : ℕ := relRamIdx w 𝔭 with he
  have ha : log (w.maximalIdeal.valuation _ (genC' P x)) =
      e * log (𝔭.maximalIdeal.valuation _ (genT P x)) := by
    rw [← algebraMap_genT, valuation_algebraMap_eq_pow hw𝔭, log_pow, nsmul_eq_mul]
  have hb : log (w.maximalIdeal.valuation _ (genC' P x - 1)) =
      e * log (𝔭.maximalIdeal.valuation _ (genT P x - 1)) := by
    rw [← algebraMap_genT, ← map_one (algebraMap (tpd P x) (P.curve x).F), ← map_sub,
      valuation_algebraMap_eq_pow hw𝔭, log_pow, nsmul_eq_mul]
  rw [ha, hb, abs_mul, abs_mul, Nat.abs_cast] at hn
  -- the bound of the compactly bounded subset at `𝔭`
  obtain ⟨hA, hB⟩ := abs_log_valuation_mul_le P x hx 𝔭 (by rw [h𝔭2]; exact K.two_mem)
  rw [h𝔭2] at hA hB
  -- the residue degrees and local degrees
  have hf : (inertDeg (P.curve x).F w : ℝ) = inertDeg (tpd P x) 𝔭 * relInertDeg w 𝔭 := by
    rw [inertDeg_eq_mul hw𝔭]; push_cast; ring
  have hd : (localDeg (P.curve x).F w : ℝ) = localDeg (tpd P x) 𝔭 * (e * relInertDeg w 𝔭) := by
    rw [localDeg_eq_mul hw𝔭]; push_cast; ring
  have hD : (1 : ℝ) ≤ localDeg (tpd P x) 𝔭 := by
    exact_mod_cast Nat.mul_pos (ramIdx_pos' 𝔭) (inertDeg_pos' 𝔭)
  have hn' : ((P.tate x).qOrder w hw : ℝ) ≤ 2 * e *
      (|((log (𝔭.maximalIdeal.valuation _ (genT P x)) : ℤ) : ℝ)| +
        |((log (𝔭.maximalIdeal.valuation _ (genT P x - 1)) : ℤ) : ℝ)|) := by
    have h := (Int.cast_le (R := ℝ)).mpr hn
    push_cast at h
    linarith
  rw [hw2, hf, hd]
  exact term_le_aux hn' hA hB (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (log_natCast_nonneg _) hD hc

end AbcAdaptation.Tripod

end TwoAdicLocalTerm

section TwoAdicBound

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum WithZero WeierstrassCurve
open scoped WithZero Real Classical

variable (P : CurveProviders) (x : Pt)

theorem twoAdicBound' (K : CompactlyBounded) : TwoAdicBoundHyp P K (4 * K.c) := by
  intro x hx
  classical
  have hc := CompactlyBounded.c_nonneg hx
  change (∑ w ∈ (P.arith x).badAll_finite.toFinset.filter (fun w => AbcAdaptation.Reference.Iut.residueChar w = 2),
      (((if h : w ∈ (P.curve x).badAll then (P.tate x).qOrder w h else 0 : ℕ) : ℝ) *
        (inertDeg (P.curve x).F w : ℝ) * Real.log (AbcAdaptation.Reference.Iut.residueChar w))) /
      (Module.finrank ℚ (P.curve x).F : ℝ) ≤ 4 * K.c
  rw [div_le_iff₀ (by exact_mod_cast Module.finrank_pos)]
  calc ∑ w ∈ (P.arith x).badAll_finite.toFinset.filter (fun w => AbcAdaptation.Reference.Iut.residueChar w = 2),
        (((if h : w ∈ (P.curve x).badAll then (P.tate x).qOrder w h else 0 : ℕ) : ℝ) *
          (inertDeg (P.curve x).F w : ℝ) * Real.log (AbcAdaptation.Reference.Iut.residueChar w))
      ≤ ∑ w ∈ (P.arith x).badAll_finite.toFinset.filter (fun w => AbcAdaptation.Reference.Iut.residueChar w = 2),
          4 * K.c * (localDeg (P.curve x).F w : ℝ) := by
        refine Finset.sum_le_sum fun w hw => ?_
        rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hw
        split_ifs with h
        · exact term_le P x hx h hw.2
        · exact absurd hw.1 h
    _ = 4 * K.c * ∑ w ∈ (P.arith x).badAll_finite.toFinset.filter (fun w => AbcAdaptation.Reference.Iut.residueChar w = 2),
          (localDeg (P.curve x).F w : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 4 * K.c * (Module.finrank ℚ (P.curve x).F : ℝ) := by
        let S : Finset (FinitePlace (P.curve x).F) := (P.arith x).badAll_finite.toFinset
        have hcast : ((∑ w ∈ S.filter (fun w => AbcAdaptation.Reference.Iut.residueChar w = 2),
            localDeg (P.curve x).F w : ℕ) : ℝ) ≤ (Module.finrank ℚ (P.curve x).F : ℝ) :=
          Nat.cast_le.mpr (sum_localDeg_filter_le S 2)
        have hsum := (Nat.cast_sum (R := ℝ) (S.filter fun w => AbcAdaptation.Reference.Iut.residueChar w = 2)
          (localDeg (P.curve x).F)).symm.trans_le hcast
        exact mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hc)

end AbcAdaptation.Tripod

end TwoAdicBound

section TwoAdicSolution

set_option autoImplicit false

open AbcAdaptation.Tripod

theorem solution (P : CurveProviders) (K : CompactlyBounded) :
    TwoAdicBoundHyp P K (max (4 * K.c) 0) :=
  fun x hx => (twoAdicBound' P K x hx).trans (le_max_left _ _)

end TwoAdicSolution

section TwoAdicPlatformStatement

open AbcAdaptation.Tripod

theorem AbcAdaptation.Tripod.twoAdicBound (P : CurveProviders) (K : CompactlyBounded) :
    TwoAdicBoundHyp P K (max (4 * K.c) 0) :=
  solution P K

#print axioms AbcAdaptation.Reference.Iut.LocalHeightData.heightEq
#print axioms TwoAdicBoundHyp
#print axioms twoAdicBound'
#print axioms twoAdicBound
#print axioms solution

end TwoAdicPlatformStatement
