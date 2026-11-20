/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/M2/Final.lean
-/
import Mathlib.NumberTheory.Padics.PadicNorm

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2

/-- A rational number with p-adic norm at most one at every prime is an integer. -/
theorem exists_int_of_padicNorm_le_one {q : ℚ}
    (h : ∀ p : ℕ, p.Prime → padicNorm p q ≤ 1) : ∃ m : ℤ, q = (m : ℚ) := by
  by_cases hden : q.den = 1
  · exact ⟨q.num, (Rat.coe_int_num_of_den_eq_one hden).symm⟩
  exfalso
  let p := q.den.minFac
  have hp : p.Prime := Nat.minFac_prime hden
  letI : Fact p.Prime := ⟨hp⟩
  have hpd : p ∣ q.den := Nat.minFac_dvd _
  have hnum : ¬(p : ℤ) ∣ q.num := by
    intro hdvd
    have hgcd := Nat.dvd_gcd (Int.natCast_dvd.mp hdvd) hpd
    rw [q.reduced] at hgcd
    exact hp.ne_one (Nat.dvd_one.mp hgcd)
  have hnumNorm : padicNorm p (q.num : ℚ) = 1 := (padicNorm.int_eq_one_iff q.num).2 hnum
  have hdenNorm : padicNorm p (q.den : ℚ) < 1 := (padicNorm.nat_lt_one_iff q.den).2 hpd
  have hdenNonzero : padicNorm p (q.den : ℚ) ≠ 0 :=
    padicNorm.nonzero (Nat.cast_ne_zero.mpr q.den_nz)
  have hdenPos : 0 < padicNorm p (q.den : ℚ) :=
    lt_of_le_of_ne (padicNorm.nonneg _) hdenNonzero.symm
  have hlarge : 1 < padicNorm p q := calc
    1 < 1 / padicNorm p (q.den : ℚ) := (one_lt_div₀ hdenPos).2 hdenNorm
    _ = padicNorm p ((q.num : ℚ) / (q.den : ℚ)) := by rw [padicNorm.div, hnumNorm]
    _ = padicNorm p q := congrArg (padicNorm p) q.num_div_den
  exact (not_lt_of_ge (h p hp)) hlarge

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2
