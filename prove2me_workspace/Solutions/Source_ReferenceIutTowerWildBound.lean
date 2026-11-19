/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 2d8f000457da6447fa4df4bfec7365c1a49b6384
Original path Iut/Tower/WildBound.lean
-/
import Solutions.Source_ReferenceIutTowerLocalFacts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

private theorem padicValNat_card_GL_two {ℓ : ℕ} (hℓ : ℓ.Prime) :
    padicValNat ℓ ((ℓ ^ 2 - 1) * (ℓ ^ 2 - ℓ)) = 1 := by
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  have h2 := hℓ.two_le
  have hsq : 1 < ℓ ^ 2 := by nlinarith
  have hfactor : ℓ ^ 2 - ℓ = ℓ * (ℓ - 1) := by rw [Nat.mul_sub, mul_one, sq]
  have h₁ : ¬ ℓ ∣ ℓ ^ 2 - 1 := by
    intro h
    have hone := Nat.dvd_sub (dvd_pow_self ℓ two_ne_zero) h
    rw [Nat.sub_sub_self hsq.le] at hone
    exact hℓ.not_dvd_one hone
  have hpred : ℓ - 1 ≠ 0 := by omega
  have h₂ : ¬ ℓ ∣ ℓ - 1 := by
    intro h
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hpred) h
    omega
  rw [hfactor, padicValNat.mul (Nat.sub_ne_zero_of_lt hsq)
    (Nat.mul_ne_zero hℓ.ne_zero hpred), padicValNat.mul hℓ.ne_zero hpred,
    padicValNat.eq_zero_of_not_dvd h₁, padicValNat.eq_zero_of_not_dvd h₂, padicValNat_self]

private theorem padicValNat_prime_cases {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    padicValNat p q = if p = q then 1 else 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  split_ifs with h
  · subst q
    exact padicValNat_self
  · exact padicValNat_primes h

private theorem padicValNat_184320 {p : ℕ} (hp : p.Prime) :
    padicValNat p 184320 = if p = 2 then 12 else if p = 3 then 2 else if p = 5 then 1 else 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hfactor : (184320 : ℕ) = 2 ^ 12 * 3 ^ 2 * 5 := by decide
  rw [hfactor, padicValNat.mul (a := 2 ^ 12 * 3 ^ 2) (b := 5) (by decide) (by decide),
    padicValNat.mul (a := 2 ^ 12) (b := 3 ^ 2) (by decide) (by decide),
    padicValNat.pow 2 12, padicValNat.pow 3 2, padicValNat_prime_cases hp Nat.prime_two,
    padicValNat_prime_cases hp Nat.prime_three, padicValNat_prime_cases hp Nat.prime_five]
  by_cases h2 : p = 2
  · subst p
    decide
  by_cases h3 : p = 3
  · subst p
    decide
  by_cases h5 : p = 5
  · subst p
    decide
  simp [h2, h3, h5]

/-- The degree divisibilities and tameness bound the wild part of the tower index. -/
theorem padicValNat_mul_le_wildConst {ℓ p e₁ e₂ : ℕ} (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
    (hp : p.Prime) (h₁ : e₁ ∣ (ℓ ^ 2 - 1) * (ℓ ^ 2 - ℓ)) (h₂ : e₂ ∣ 184320)
    (htame : p ≠ ℓ → ¬ p ∣ e₁) :
    padicValNat p (e₁ * e₂) ≤ wildConst ℓ p := by
  letI : Fact p.Prime := ⟨hp⟩
  have hGL : (ℓ ^ 2 - 1) * (ℓ ^ 2 - ℓ) ≠ 0 := by
    have h2 := hℓ.two_le
    exact Nat.mul_ne_zero (Nat.sub_ne_zero_of_lt (by nlinarith))
      (Nat.sub_ne_zero_of_lt (by nlinarith))
  have he₁ := ne_zero_of_dvd_ne_zero hGL h₁
  have he₂ := ne_zero_of_dvd_ne_zero (by decide : (184320 : ℕ) ≠ 0) h₂
  have hv₁ : padicValNat p e₁ ≤ padicValNat p ((ℓ ^ 2 - 1) * (ℓ ^ 2 - ℓ)) :=
    (padicValNat_dvd_iff_le hGL).mp (pow_padicValNat_dvd.trans h₁)
  have hv₂ : padicValNat p e₂ ≤ padicValNat p 184320 :=
    (padicValNat_dvd_iff_le (by decide)).mp (pow_padicValNat_dvd.trans h₂)
  rw [padicValNat_184320 hp] at hv₂
  rw [padicValNat.mul he₁ he₂]
  by_cases hpℓ : p = ℓ
  · subst p
    have h2 : ℓ ≠ 2 := by omega
    have h3 : ℓ ≠ 3 := by omega
    have h5 : ℓ ≠ 5 := by omega
    rw [padicValNat_card_GL_two hℓ] at hv₁
    rw [if_neg h2, if_neg h3, if_neg h5] at hv₂
    have hz : padicValNat ℓ e₂ = 0 := Nat.eq_zero_of_le_zero hv₂
    rw [hz, add_zero]
    simpa [wildConst, h2, h3, h5] using hv₁
  · rw [padicValNat.eq_zero_of_not_dvd (htame hpℓ), zero_add, wildConst, if_neg hpℓ, add_zero]
    exact hv₂

end AbcAdaptation.Reference.Iut
