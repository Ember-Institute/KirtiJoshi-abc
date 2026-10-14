import ArithmeticTeichmullerSpaces.Act1Scene1.LocalPadicLogBounded
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerRootDescent
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.CharP.Lemmas

/-!
source-id: JT-SCENE1-LOCAL-PADIC-KUMMER-NONVANISHING
source: local-field Kummer nonvanishing for a principal unit with nonzero log.
fidelity: residue characteristic p forces p-power roots of principal units
to remain principal. The uniform log bound then excludes arbitrarily deep
roots when the ordinary log is nonzero. Root descent proves the standard
integral Kummer class nonzero, without assuming H^1_e or BK comparison.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalPadicLog
open Filter Topology
open scoped Valued
universe u v
noncomputable section
variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
variable {p : ℕ}

theorem norm_sub_one_lt_of_pow_prime_pow (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
    {x : k} (n : ℕ) (hx : ‖x ^ (p ^ n) - 1‖ < 1) : ‖x - 1‖ < 1 := by
  have hnx : ‖x‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg x) (pow_ne_zero n hp.ne_zero)).mp
    (by rw [← norm_pow]; exact norm_eq_one_of_norm_sub_one_lt hx)
  let A := (Valued.v : Valuation k (WithZero (Multiplicative ℤ))).valuationSubring
  let z : A := ⟨x, (Valued.toNormedField.norm_le_one_iff).mp hnx.le⟩
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : (p : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff,
      Valuation.mem_maximalIdeal_iff]
    exact (Valued.toNormedField.norm_lt_one_iff).mp hpk
  letI : CharP (IsLocalRing.ResidueField A) p := (CharP.charP_iff_prime_eq_zero hp).mpr hp0
  have he : IsLocalRing.residue A (z ^ (p ^ n) - 1) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
    exact (Valued.toNormedField.norm_lt_one_iff).mp hx
  have hz : (IsLocalRing.residue A z - 1) ^ (p ^ n) = 0 := by
    rw [sub_pow_char_pow, one_pow]
    simpa only [map_sub, map_pow, map_one] using he
  have hr : IsLocalRing.residue A (z - 1) = 0 := by
    rw [map_sub, map_one]
    exact eq_zero_of_pow_eq_zero hz
  rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff] at hr
  exact (Valued.toNormedField.norm_lt_one_iff).mpr hr

variable [CharZero k] [CompleteSpace k]

theorem padicLog_eq_zero_of_all_prime_power_roots (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
    {a : k} (ha : ‖a - 1‖ < 1) (hroot : ∀ n : ℕ, ∃ b : k, b ^ (p ^ n) = a) :
    padicLog a = 0 := by
  obtain ⟨M, hM0, hM⟩ := exists_forall_norm_padicLog_le hp hpk
  have hb (n : ℕ) : ‖padicLog a‖ ≤ ‖(p : k)‖ ^ n * M := by
    obtain ⟨b, hba⟩ := hroot n
    have hbsmall : ‖b - 1‖ < 1 := norm_sub_one_lt_of_pow_prime_pow hp hpk n (by rwa [hba])
    have he : padicLog a = (p : k) ^ n * padicLog b := by
      rw [← hba, padicLog_pow hp hpk hbsmall, Nat.cast_pow]
    rw [he, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (hM b hbsmall) (pow_nonneg (norm_nonneg _) _)
  have ht : Tendsto (fun n : ℕ => ‖(p : k)‖ ^ n * M) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (p : k)) hpk).mul_const M
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto ht (Eventually.of_forall hb)) (norm_nonneg _))

theorem exists_no_prime_power_root_of_log_ne_zero (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
    {a : k} (ha : ‖a - 1‖ < 1) (hlog : padicLog a ≠ 0) :
    ∃ n : ℕ, ¬ ∃ b : k, b ^ (p ^ n) = a := by
  by_contra! h
  exact hlog (padicLog_eq_zero_of_all_prime_power_roots hp hpk ha h)

variable {Ω : Type v} [Field Ω] [Algebra k Ω] [IsGalois k Ω] [Algebra.IsIntegral k Ω]
variable [Fact p.Prime]

theorem integralKummer_ne_zero_of_log_ne_zero {a : k}
    (R : LocalKummer.RootTower (Ω := Ω) p a) (hpk : ‖(p : k)‖ < 1)
    (ha : ‖a - 1‖ < 1) (hlog : padicLog a ≠ 0) :
    LocalKummer.padicClassOfCocycle p
      (R.continuousCocycleValue (Fact.out : p.Prime).pos (ne_zero_of_norm_sub_one_lt ha)) ≠ 0 := by
  obtain ⟨n, hn⟩ := exists_no_prime_power_root_of_log_ne_zero (Fact.out : p.Prime) hpk ha hlog
  exact R.padicClass_ne_zero_of_no_root (ne_zero_of_norm_sub_one_lt ha) n hn

end
end JoshiTeich.Act1Scene1.LocalPadicLog
