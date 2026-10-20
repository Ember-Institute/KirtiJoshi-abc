import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Prime.Lemmas

/-!
source-id: JT-SCENE1-PRIME-ADIC-SEPARATION
source: Joshi II principal Fontaine kernel and its B_dR completion
(838, 932, 1069--1076); Mathlib adic separation and prime-power cancellation.
fidelity: derives xi-adic separation from p-adic separation, an actual
mod-p intersection criterion, and primality of xi with xi not dividing p.
Proves that this separation survives localization at p by clearing
denominators. No Noetherian assumption or completion-injectivity certificate.
Original proofs; Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.PrimeAdicSeparation

noncomputable section
variable {R : Type*} [CommRing R] [IsDomain R]

/-- Infinite xi-divisibility and mod-p detection force infinite p-divisibility. -/
theorem of_mod_p (p ξ : R) [IsHausdorff (Ideal.span {p}) R]
    (hξ : Prime ξ) (hcop : ¬ ξ ∣ p)
    (hmod : ∀ a : R, (∀ n : ℕ, ξ ^ n ∣ a) → p ∣ a) :
    IsHausdorff (Ideal.span {ξ}) R := by
  have hdivide (a : R) (ha : ∀ n : ℕ, ξ ^ n ∣ a) :
      ∃ b : R, (∀ n : ℕ, ξ ^ n ∣ b) ∧ a = p * b := by
    obtain ⟨b, hb⟩ := hmod a ha
    refine ⟨b, fun n => hξ.pow_dvd_of_dvd_mul_left n hcop ?_, hb⟩
    rw [← hb]
    exact ha n
  have hpowers (n : ℕ) : ∀ a : R, (∀ m : ℕ, ξ ^ m ∣ a) → p ^ n ∣ a := by
    induction n with
    | zero => intro a _; simp only [pow_zero, one_dvd]
    | succ n ih =>
        intro a ha
        obtain ⟨b, hb, hab⟩ := hdivide a ha
        obtain ⟨c, hc⟩ := ih b hb
        refine ⟨c, ?_⟩
        rw [hab, hc, pow_succ', mul_assoc]
  constructor
  intro a ha
  have hξa (n : ℕ) : ξ ^ n ∣ a := by
    have h := SModEq.zero.mp (ha n)
    simpa only [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] using h
  apply IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {p}) R) a
  intro n
  apply SModEq.zero.mpr
  simpa only [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] using hpowers n a hξa

variable (S : Type*) [CommRing S] [Algebra R S]
variable (p ξ : R) [IsLocalization.Away p S]

theorem away_injective (hp : p ≠ 0) : Function.Injective (algebraMap R S) := by
  apply IsLocalization.injective (M := Submonoid.powers p)
  rintro x ⟨n, rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hp)

/-- Prime powers are saturated under the denominators being inverted. -/
theorem pow_dvd_of_localized_dvd (hp : p ≠ 0) (hξ : Prime ξ) (hcop : ¬ ξ ∣ p)
    (n : ℕ) (a : R) (ha : (algebraMap R S ξ) ^ n ∣ algebraMap R S a) :
    ξ ^ n ∣ a := by
  obtain ⟨b, hb⟩ := ha
  obtain ⟨m, c, hc⟩ := IsLocalization.Away.surj p b
  apply hξ.pow_dvd_of_dvd_mul_left n (fun h => hcop (hξ.dvd_of_dvd_pow h))
  refine ⟨c, ?_⟩
  apply away_injective S p hp
  rw [map_mul, map_pow, map_mul, map_pow, mul_comm ((algebraMap R S) p ^ m), hb,
    mul_assoc, hc]

theorem away (hp : p ≠ 0) (hξ : Prime ξ) (hcop : ¬ ξ ∣ p)
    [IsHausdorff (Ideal.span {ξ}) R] :
    IsHausdorff (Ideal.span {algebraMap R S ξ}) S := by
  constructor
  intro x hx
  obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj p x
  have hdiv (n : ℕ) : (algebraMap R S ξ) ^ n ∣ x := by
    have h := SModEq.zero.mp (hx n)
    simpa only [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] using h
  have ha0 : a = 0 := by
    apply IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {ξ}) R) a
    intro n
    apply SModEq.zero.mpr
    simp only [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    apply pow_dvd_of_localized_dvd S p ξ hp hξ hcop n a
    rw [← ha]
    exact (hdiv n).mul_right _
  have he : x * (algebraMap R S p) ^ m = 0 := by rw [ha, ha0, map_zero]
  exact ((IsLocalization.Away.algebraMap_isUnit p (S := S)).pow m).mul_left_eq_zero.mp he

end
end JoshiTeich.Act1Scene1.PrimeAdicSeparation
