import ArithmeticTeichmullerSpaces.Act1Scene1.LocalPadicLog

/-!
source-id: JT-SCENE1-LOCAL-PSTAR-LOG
source: Joshi III p* (3160--3175), eq:bloch-kato-log-class (3226)
and le:elem-lemma (3394--3430).
fidelity: constructs the ordinary convergent expression log(1+pStar*y)/pStar
with p* equal to p at odd primes and 4 at 2. It proves the principal-unit
condition and the norm identity. No cohomology class or BK comparison is
defined by renaming this ordinary logarithm.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalPadicLog
open scoped Valued
universe u
noncomputable section

def paperScale (p : ℕ) : ℕ := if p = 2 then 4 else p

theorem paperScale_ne_zero {p : ℕ} (hp : p.Prime) : paperScale p ≠ 0 := by
  unfold paperScale
  split_ifs
  · norm_num
  · exact hp.ne_zero

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
  [CharZero k] [CompleteSpace k] {p : ℕ}

theorem norm_paperScale_eq_norm_two_mul (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) :
    ‖(paperScale p : k)‖ = ‖2 * (p : k)‖ := by
  by_cases h : p = 2
  · subst p
    norm_num [paperScale]
  · have hn := norm_two_eq_one hp hpk (hp.odd_of_ne_two h)
    simp only [paperScale, if_neg h, norm_mul, hn, one_mul]

def paperPrincipalUnit (p : ℕ) (y : k) : k := 1 + (paperScale p : k) * y

def paperNormalizedLog (p : ℕ) (y : k) : k :=
  (paperScale p : k)⁻¹ * padicLog (paperPrincipalUnit p y)

theorem paperPrincipalUnit_norm_sub_one_lt_one
    (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {y : k} (hy : ‖y‖ ≤ 1) :
    ‖paperPrincipalUnit p y - 1‖ < 1 := by
  simp only [paperPrincipalUnit, add_sub_cancel_left, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) hy).trans_lt
    ((norm_paperScale_eq_norm_two_mul hp hpk).trans_lt (norm_two_mul_lt_one hpk))

theorem paperPrincipalUnit_ne_zero
    (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {y : k} (hy : ‖y‖ ≤ 1) :
    paperPrincipalUnit p y ≠ 0 := by
  intro h
  have hn := paperPrincipalUnit_norm_sub_one_lt_one hp hpk hy
  simpa only [h, zero_sub, norm_neg, norm_one, lt_self_iff_false] using hn

theorem norm_paperNormalizedLog
    (hp : p.Prime) (hpk : ‖(p : k)‖ < 1) {y : k} (hy : ‖y‖ ≤ 1) :
    ‖paperNormalizedLog p y‖ = ‖y‖ := by
  have hs : (paperScale p : k) ≠ 0 := Nat.cast_ne_zero.mpr (paperScale_ne_zero hp)
  have hsmall : ‖(paperScale p : k) * y‖ ≤ ‖2 * (p : k)‖ := by
    rw [norm_mul, norm_paperScale_eq_norm_two_mul hp hpk]
    exact mul_le_of_le_one_right (norm_nonneg _) hy
  rw [paperNormalizedLog, paperPrincipalUnit, norm_mul, norm_inv,
    norm_padicLog_one_add hp hpk hsmall, norm_mul, ← mul_assoc,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hs), one_mul]

end
end JoshiTeich.Act1Scene1.LocalPadicLog
