import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerImageLogKernel
import Mathlib.NumberTheory.Padics.RingHoms

/-!
source-id: JT-SCENE1-PRINCIPAL-UNIT-PADIC-POWER
source: actual principal-unit p-power convergence, PadicInt.appr congruences,
and ordinary logarithm multiplication/small-ball laws; Joshi III 3212--3226.
fidelity: constructs a principal-unit p-adic power by limits of integer powers,
proves logarithm continuity at principal units and its scalar limit formula.
No scalar action on H1 is defined here; Kummer/cocycle scalar comparison,
Q_p closure and H1e/BK identification remain separate obligations.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalPadicLog
open Filter Topology
open scoped Valued
universe u
noncomputable section
variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
variable [CharZero k] [CompleteSpace k] {p : ℕ} [Fact p.Prime]

theorem norm_principal_pow_sub_one_le {a : k} (ha : ‖a - 1‖ < 1) (m : ℕ) :
    ‖a ^ m - 1‖ ≤ ‖a - 1‖ := by
  induction m with
  | zero => simpa using norm_nonneg (a - 1)
  | succ m ih =>
    have he : a ^ (m + 1) - 1 = a ^ m * (a - 1) + (a ^ m - 1) := by ring
    rw [he]
    apply (IsUltrametricDist.norm_add_le_max _ _).trans
    apply max_le _ ih
    rw [norm_mul, norm_pow, norm_eq_one_of_norm_sub_one_lt ha, one_pow, one_mul]

theorem principal_pow_dist_le_of_dvd {a : k} (ha : ‖a - 1‖ < 1)
    {m n N : ℕ} (hmn : m ≤ n) (hd : p ^ N ∣ n - m) :
    dist (a ^ m) (a ^ n) ≤ ‖a ^ (p ^ N) - 1‖ := by
  obtain ⟨d, hd⟩ := hd
  have hn : n = m + p ^ N * d := by omega
  rw [dist_comm, dist_eq_norm, hn, pow_add,
    show a ^ m * a ^ (p ^ N * d) - a ^ m = a ^ m * (a ^ (p ^ N * d) - 1) by ring,
    norm_mul, norm_pow, norm_eq_one_of_norm_sub_one_lt ha, one_pow, one_mul, pow_mul]
  exact norm_principal_pow_sub_one_le (norm_pow_sub_one_lt ha (p ^ N)) d

theorem principal_appr_powers_cauchy (hpk : ‖(p : k)‖ < 1)
    {a : k} (ha : ‖a - 1‖ < 1) (r : ℤ_[p]) :
    CauchySeq (fun n : ℕ => a ^ r.appr n) := by
  apply cauchySeq_of_le_tendsto_0' (fun N => ‖a ^ (p ^ N) - 1‖)
  · intro m n hmn
    exact principal_pow_dist_le_of_dvd ha (r.appr_mono hmn) (r.dvd_appr_sub_appr m n hmn)
  · simpa only [norm_zero] using
      (tendsto_principal_prime_power_sub_one (Fact.out : p.Prime) hpk ha).norm

/-- Existence includes a uniform distance bound, so the limit remains principal. -/
theorem exists_principal_appr_power_limit (hpk : ‖(p : k)‖ < 1)
    {a : k} (ha : ‖a - 1‖ < 1) (r : ℤ_[p]) :
    ∃ b : k, Tendsto (fun n : ℕ => a ^ r.appr n) atTop (𝓝 b) ∧
      ‖b - 1‖ ≤ ‖a - 1‖ := by
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete (principal_appr_powers_cauchy hpk ha r)
  refine ⟨b, hb, ?_⟩
  exact le_of_tendsto (hb.sub_const 1).norm (Filter.Eventually.of_forall
    fun n => norm_principal_pow_sub_one_le ha (r.appr n))

def principalPadicPower (hpk : ‖(p : k)‖ < 1) (a : principalUnits (k := k))
    (r : ℤ_[p]) : principalUnits (k := k) := by
  let b := Classical.choose (exists_principal_appr_power_limit hpk a.2 r)
  have hb : ‖b - 1‖ < 1 :=
    (Classical.choose_spec (exists_principal_appr_power_limit hpk a.2 r)).2.trans_lt a.2
  exact ⟨Units.mk0 b (ne_zero_of_norm_sub_one_lt hb), hb⟩

theorem tendsto_principalPadicPower (hpk : ‖(p : k)‖ < 1)
    (a : principalUnits (k := k)) (r : ℤ_[p]) :
    Tendsto (fun n : ℕ => (a.1 : k) ^ r.appr n) atTop
      (𝓝 ((principalPadicPower hpk a r).1 : k)) :=
  (Classical.choose_spec (exists_principal_appr_power_limit hpk a.2 r)).1

/-- Close principal units have logarithms at exactly the same distance. -/
theorem norm_padicLog_sub_eq_of_dist_le (hpk : ‖(p : k)‖ < 1)
    {a b : k} (ha : ‖a - 1‖ < 1) (hb : ‖b - 1‖ < 1)
    (hab : ‖a - b‖ ≤ ‖2 * (p : k)‖) :
    ‖padicLog a - padicLog b‖ = ‖a - b‖ := by
  have hb0 := ne_zero_of_norm_sub_one_lt hb
  have hratio : a / b - 1 = (a - b) / b := by field_simp
  have hnorm : ‖a / b - 1‖ = ‖a - b‖ := by
    rw [hratio, norm_div, norm_eq_one_of_norm_sub_one_lt hb, div_one]
  have h := norm_padicLog_one_add (Fact.out : p.Prime) hpk (hnorm.le.trans hab)
  rw [add_sub_cancel] at h
  have hlog : padicLog (a / b) = padicLog a - padicLog b := by
    rw [div_eq_mul_inv, padicLog_mul (Fact.out : p.Prime) hpk ha (norm_inv_sub_one_lt hb),
      padicLog_inv (Fact.out : p.Prime) hpk hb, sub_eq_add_neg]
  rw [hlog, hnorm] at h
  exact h

theorem continuousAt_padicLog_principal (hpk : ‖(p : k)‖ < 1)
    {a : k} (ha : ‖a - 1‖ < 1) : ContinuousAt padicLog a := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨min ε (min (1 : ℝ) ‖2 * (p : k)‖),
    lt_min hε (lt_min zero_lt_one (norm_pos_iff.mpr
      (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)))), ?_⟩
  intro b hb
  rw [dist_eq_norm] at hb
  have hb1 : ‖b - 1‖ < 1 := by
    have he : b - 1 = (b - a) + (a - 1) := by ring
    rw [he]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
      (max_lt ((lt_min_iff.mp (lt_min_iff.mp hb).2).1) ha)
  rw [dist_eq_norm, norm_padicLog_sub_eq_of_dist_le hpk hb1 ha
    ((lt_min_iff.mp (lt_min_iff.mp hb).2).2.le)]
  exact (lt_min_iff.mp hb).1

/-- PadicInt.appr converges in its actual p-adic topology. -/
theorem tendsto_padicInt_appr (r : ℤ_[p]) :
    Tendsto (fun n : ℕ => (r.appr n : ℤ_[p])) atTop (𝓝 r) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (g := fun n : ℕ => (p : ℝ) ^ (-(n : ℤ))) (fun n => dist_nonneg)
    (fun n => by
      change ‖(r.appr n : ℤ_[p]) - r‖ ≤ _
      rw [norm_sub_rev]
      exact (PadicInt.norm_le_pow_iff_mem_span_pow _ n).mpr (r.appr_spec n))
  have hp : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  simpa only [zpow_neg, zpow_natCast, ← inv_pow] using
    tendsto_pow_atTop_nhds_zero_of_lt_one hp hp1

variable [Algebra ℚ_[p] k] [ContinuousSMul ℚ_[p] k]

/-- The scalar action here is the pre-existing continuous Q_p action on k. -/
theorem padicLog_principalPadicPower (hpk : ‖(p : k)‖ < 1)
    (a : principalUnits (k := k)) (r : ℤ_[p]) :
    padicLog ((principalPadicPower hpk a r).1 : k) = (r : ℚ_[p]) • padicLog (a.1 : k) := by
  have hl := (continuousAt_padicLog_principal hpk (principalPadicPower hpk a r).2).tendsto.comp
    (tendsto_principalPadicPower hpk a r)
  have hr : Tendsto (fun n : ℕ => ((r.appr n : ℕ) : ℚ_[p])) atTop (𝓝 (r : ℚ_[p])) := by
    have hcast : Continuous (PadicInt.Coe.ringHom : ℤ_[p] → ℚ_[p]) := by
      exact continuous_subtype_val
    exact hcast.continuousAt.tendsto.comp (tendsto_padicInt_appr r)
  have hs := hr.smul_const (padicLog (a.1 : k))
  apply tendsto_nhds_unique hl
  exact hs.congr fun n => by
    change ((r.appr n : ℕ) : ℚ_[p]) • padicLog (a.1 : k) =
      padicLog ((a.1 : k) ^ r.appr n)
    rw [padicLog_pow (Fact.out : p.Prime) hpk a.2, Nat.cast_smul_eq_nsmul ℚ_[p], nsmul_eq_mul]

end
end JoshiTeich.Act1Scene1.LocalPadicLog
