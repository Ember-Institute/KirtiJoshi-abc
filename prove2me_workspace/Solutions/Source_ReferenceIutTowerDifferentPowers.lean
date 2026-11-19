/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Tower/DifferentBound.lean and Iut/Tower/SerreBound.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory
import Solutions.Source_ReferenceIutTowerIdealOrder
import Solutions.Source_TripodFinitePlaceArithmetic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace Serre

section Elementary

variable {A : Type*} [CommRing A] (𝔭 : Ideal A) [𝔭.IsMaximal]

/-- `𝔭 + (s) = 1` for `s ∉ 𝔭`. -/
lemma sup_span_singleton_eq_top {s : A} (hs : s ∉ 𝔭) : 𝔭 ⊔ Ideal.span {s} = ⊤ := by
  by_contra h
  have := Ideal.IsMaximal.eq_of_le ‹𝔭.IsMaximal› h le_sup_left
  exact hs (this ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))

/-- `s ∉ 𝔭`, `s·a ∈ 𝔭^n` ⟹ `a ∈ 𝔭^n`. -/
lemma mem_pow_of_mul_mem_pow {s a : A} (hs : s ∉ 𝔭) (n : ℕ) (h : s * a ∈ 𝔭 ^ n) :
    a ∈ 𝔭 ^ n := by
  have hcop : IsCoprime (𝔭 ^ n) (Ideal.span {s}) :=
    (Ideal.isCoprime_iff_sup_eq.mpr (sup_span_singleton_eq_top 𝔭 hs)).pow_left
  obtain ⟨x, hx, y, hy, hxy⟩ := hcop.exists
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  have : a = a * x + c * (s * a) := by
    calc a = a * (x + c * s) := by rw [hxy, mul_one]
      _ = a * x + c * (s * a) := by ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_left _ _ h)

/-- For coprime ideals `I`, `J` there is `w ∈ J` with `1 − w ∈ I`. -/
lemma exists_mem_and_one_sub_mem {R : Type*} [CommRing R] {I J : Ideal R} (h : IsCoprime I J) :
    ∃ w ∈ J, 1 - w ∈ I := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h.exists
  exact ⟨y, hy, by rw [← hxy, add_sub_cancel_right]; exact hx⟩

end Elementary

end Serre

section Powers

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- `a^m ∉ 𝔓^{em+1}` for `a ∈ 𝔓^e ∖ 𝔓^{e+1}`, `𝔓` a nonzero prime of a Dedekind domain. -/
lemma pow_notMem_pow_mul_succ (𝔓 : Ideal R) [𝔓.IsPrime] (h𝔓 : 𝔓 ≠ ⊥) {a : R} {e : ℕ}
    (ha : a ∈ 𝔓 ^ e) (ha' : a ∉ 𝔓 ^ (e + 1)) (m : ℕ) : a ^ m ∉ 𝔓 ^ (e * m + 1) := by
  intro h
  have hprime : Prime 𝔓 := Ideal.prime_of_isPrime h𝔓 inferInstance
  obtain ⟨𝔞, h𝔞⟩ : 𝔓 ^ e ∣ Ideal.span {a} := Ideal.dvd_span_singleton.mpr ha
  have h1 : 𝔓 ^ (e * m + 1) ∣ Ideal.span {a} ^ m := by
    rw [Ideal.span_singleton_pow]
    exact Ideal.dvd_span_singleton.mpr h
  rw [h𝔞, mul_pow, pow_succ, ← pow_mul] at h1
  have h2 : 𝔓 ∣ 𝔞 ^ m := (mul_dvd_mul_iff_left (pow_ne_zero _ h𝔓)).mp h1
  have h3 : 𝔓 ∣ 𝔞 := hprime.dvd_of_dvd_pow h2
  apply ha'
  rw [← Ideal.dvd_span_singleton, h𝔞, pow_succ]
  exact mul_dvd_mul_left _ h3

end Powers

section Serre

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The residue characteristic `p` of `u` lies in `𝔭_u^{e_u}` and not in `𝔭_u^{e_u+1}`. -/
lemma residueChar_mem_pow_ramIdx (u : FinitePlace k) :
    ((residueChar u : ℕ) : 𝓞 k) ∈ u.maximalIdeal.asIdeal ^ ramIdx k u ∧
      ((residueChar u : ℕ) : 𝓞 k) ∉ u.maximalIdeal.asIdeal ^ (ramIdx k u + 1) := by
  letI : u.maximalIdeal.asIdeal.LiesOver (Ideal.span {(residueChar u : ℤ)} : Ideal ℤ) :=
    Tripod.liesOver_span_residueChar u
  have hp : (residueChar u).Prime := Tripod.residueChar_prime u
  have hp0 : (Ideal.span {(residueChar u : ℤ)} : Ideal ℤ) ≠ ⊥ :=
    Tripod.under_int_eq u ▸ Tripod.under_int_ne_bot u
  haveI : (Ideal.span {(residueChar u : ℤ)}).IsMaximal :=
    Tripod.under_int_eq u ▸ Tripod.under_int_isMaximal u
  have h𝔭 : u.maximalIdeal.asIdeal ≠ ⊥ := u.maximalIdeal.ne_bot
  have hmap : (Ideal.span {(residueChar u : ℤ)}).map (algebraMap ℤ (𝓞 k)) =
      Ideal.span {((residueChar u : ℕ) : 𝓞 k)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have he : ramIdx k u = (Ideal.span {(residueChar u : ℤ)}).ramificationIdx'
      u.maximalIdeal.asIdeal :=
    (Ideal.ramificationIdx'_eq_ramificationIdx
      (Ideal.span {(residueChar u : ℤ)} : Ideal ℤ) u.maximalIdeal.asIdeal hp0).symm
  have hne : Ideal.span {((residueChar u : ℕ) : 𝓞 k)} ≠ 0 := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  constructor
  · have := Ideal.le_pow_ramificationIdx' (p := Ideal.span {(residueChar u : ℤ)})
      (P := u.maximalIdeal.asIdeal)
    rw [hmap, ← he] at this
    exact this (Ideal.mem_span_singleton_self _)
  · intro h
    have h1 : u.maximalIdeal.asIdeal ^ (ramIdx k u + 1) ∣
        Ideal.span {((residueChar u : ℕ) : 𝓞 k)} := Ideal.dvd_span_singleton.mpr h
    have h2 := le_ordAt_of_pow_dvd _ hne u _ h1
    have h3 : ordAt (Ideal.span {((residueChar u : ℕ) : 𝓞 k)}) u = ramIdx k u := by
      rw [he, ordAt, Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count
        (by rw [hmap]; exact hne) u.maximalIdeal.isPrime h𝔭, hmap]
    omega

/-- `(r : 𝓞 k) ∉ 𝔭_u` for `p ∤ r`. -/
lemma natCast_notMem_of_not_dvd (u : FinitePlace k) {r : ℕ} (hpr : ¬ residueChar u ∣ r) :
    ((r : ℕ) : 𝓞 k) ∉ u.maximalIdeal.asIdeal := by
  intro hmem
  apply hpr
  have h1 : (r : ℤ) ∈ u.maximalIdeal.asIdeal.under ℤ := by
    rw [Ideal.mem_under, map_natCast]
    exact hmem
  rw [Tripod.under_int_eq, Ideal.mem_span_singleton] at h1
  exact Int.natCast_dvd_natCast.mp h1

/-- `p ∤ e / p^{v_p(e)}`. -/
lemma not_dvd_of_pow_padicValNat_mul {p e r : ℕ} [Fact p.Prime] (he : e ≠ 0)
    (hr : e = p ^ padicValNat p e * r) : ¬ p ∣ r := by
  intro hdvd
  apply pow_succ_padicValNat_not_dvd (p := p) he
  calc p ^ (padicValNat p e + 1) = p ^ padicValNat p e * p := pow_succ _ _
    _ ∣ p ^ padicValNat p e * r := mul_dvd_mul_left _ hdvd
    _ = e := hr.symm

/-- `(e : 𝓞 k) ∉ 𝔭_u^{e_u·v_p(e) + 1}` for `e ≠ 0`, `p` the residue characteristic of `u`. -/
lemma natCast_notMem_pow_ramIdx_mul_padicValNat (u : FinitePlace k) {e : ℕ} (he : e ≠ 0) :
    ((e : ℕ) : 𝓞 k) ∉
      u.maximalIdeal.asIdeal ^ (ramIdx k u * padicValNat (residueChar u) e + 1) := by
  haveI : Fact (residueChar u).Prime := ⟨Tripod.residueChar_prime u⟩
  haveI : u.maximalIdeal.asIdeal.IsMaximal :=
    u.maximalIdeal.isPrime.isMaximal u.maximalIdeal.ne_bot
  obtain ⟨hpmem, hpnot⟩ := residueChar_mem_pow_ramIdx u
  obtain ⟨r, hr⟩ : residueChar u ^ padicValNat (residueChar u) e ∣ e := pow_padicValNat_dvd
  have hr' := natCast_notMem_of_not_dvd u (not_dvd_of_pow_padicValNat_mul he hr)
  intro hmem
  have hmem' : ((r : ℕ) : 𝓞 k) * ((residueChar u : ℕ) : 𝓞 k) ^ padicValNat (residueChar u) e ∈
      u.maximalIdeal.asIdeal ^ (ramIdx k u * padicValNat (residueChar u) e + 1) := by
    rw [mul_comm ((r : ℕ) : 𝓞 k), ← Nat.cast_pow, ← Nat.cast_mul, ← hr]
    exact hmem
  exact pow_notMem_pow_mul_succ u.maximalIdeal.asIdeal u.maximalIdeal.ne_bot hpmem hpnot _
    (Serre.mem_pow_of_mul_mem_pow u.maximalIdeal.asIdeal hr' _ hmem')

end Serre

end AbcAdaptation.Reference.Iut
