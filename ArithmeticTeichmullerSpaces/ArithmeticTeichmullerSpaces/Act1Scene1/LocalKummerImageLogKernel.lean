import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerImageLogarithm

/-!
source-id: JT-SCENE1-PRINCIPAL-KUMMER-IMAGE-LOG-KERNEL
source: local principal-unit ordinary logarithm, p-power limit, and rational
Kummer cohomology used in Joshi III (3190--3236).
fidelity: proves the ordinary principal-unit log kernel consists of p-power
roots of unity. The rational Kummer map kills these elements. Its kernel
therefore equals the ordinary log kernel, and the image logarithm is injective.
No H^1_e identification, BK comparison or rational scalar closure is asserted.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalPadicLog
open Filter Topology
open scoped Valued
universe u v
noncomputable section
variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
variable [CharZero k] [CompleteSpace k] {p : ℕ}

theorem tendsto_principal_prime_power_sub_one (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
    {a : k} (ha : ‖a - 1‖ < 1) :
    Tendsto (fun n : ℕ => a ^ (p ^ n) - 1) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hpk).mul
    (tendsto_pow_sub_one_div hp hpk ha)
  rw [zero_mul] at h
  have he (n : ℕ) : (p : k) ^ n * ((a ^ (p ^ n) - 1) / (p : k) ^ n) =
      a ^ (p ^ n) - 1 := by
    exact mul_div_cancel₀ _ (pow_ne_zero n (Nat.cast_ne_zero.mpr hp.ne_zero))
  exact h.congr he

theorem padicLog_eq_zero_iff_exists_prime_power_eq_one (hp : p.Prime)
    (hpk : ‖(p : k)‖ < 1) {a : k} (ha : ‖a - 1‖ < 1) :
    padicLog a = 0 ↔ ∃ n : ℕ, a ^ (p ^ n) = 1 := by
  constructor
  · intro hlog
    have ht := (tendsto_principal_prime_power_sub_one hp hpk ha).norm
    have hr : 0 < ‖2 * (p : k)‖ := norm_pos_iff.mpr
      (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr hp.ne_zero))
    have he : ∀ᶠ n : ℕ in atTop, ‖a ^ (p ^ n) - 1‖ < ‖2 * (p : k)‖ :=
      (tendsto_order.mp ht).2 ‖2 * (p : k)‖ (by simpa only [norm_zero] using hr)
    obtain ⟨n, hn⟩ := he.exists
    have hnlog : padicLog (a ^ (p ^ n)) = 0 := by
      rw [padicLog_pow hp hpk ha, hlog, mul_zero]
    have hnorm := norm_padicLog_one_add hp hpk hn.le
    rw [add_sub_cancel, hnlog, norm_zero] at hnorm
    exact ⟨n, sub_eq_zero.mp (norm_eq_zero.mp hnorm.symm)⟩
  · rintro ⟨n, hn⟩
    exact padicLog_eq_zero_of_pow_eq_one hp hpk ha (pow_ne_zero n hp.ne_zero) hn

variable {Ω : Type v} [Field Ω] [Algebra k Ω] [IsGalois k Ω] [Algebra.IsIntegral k Ω]
variable [CharZero Ω] [IsAlgClosed Ω] (p : ℕ) [Fact p.Prime]

theorem principalKummer_eq_zero_iff_log_eq_zero (hpk : ‖(p : k)‖ < 1)
    (a : Additive (principalUnits (k := k))) :
    principalKummerHom (Ω := Ω) p a = 0 ↔ principalLogHom p hpk a = 0 := by
  constructor
  · exact principalLog_eq_zero_of_kummer_eq_zero p hpk a
  · intro hlog
    obtain ⟨n, hn⟩ := (padicLog_eq_zero_iff_exists_prime_power_eq_one
      (Fact.out : p.Prime) hpk a.toMul.2).mp hlog
    have ha : (p ^ n) • a = 0 := by
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Units.ext
      exact hn
    have hc : (p ^ n) • principalKummerHom (Ω := Ω) p a = 0 := by
      rw [← map_nsmul, ha, map_zero]
    rw [← Nat.cast_smul_eq_nsmul ℚ_[p]] at hc
    exact (smul_eq_zero.mp hc).resolve_left
      (Nat.cast_ne_zero.mpr (pow_ne_zero n (Fact.out : p.Prime).ne_zero))

theorem principalImageLog_injective (hpk : ‖(p : k)‖ < 1) :
    Function.Injective (principalImageLog (k := k) (Ω := Ω) p hpk) := by
  intro x y hxy
  obtain ⟨a, ha⟩ := (principalKummerHom (k := k) (Ω := Ω) p).rangeRestrict_surjective x
  obtain ⟨b, hb⟩ := (principalKummerHom (k := k) (Ω := Ω) p).rangeRestrict_surjective y
  subst x
  subst y
  rw [principalImageLog_class, principalImageLog_class] at hxy
  have hlog : principalLogHom p hpk (a - b) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr hxy
  have hc := (principalKummer_eq_zero_iff_log_eq_zero (Ω := Ω) p hpk (a - b)).mpr hlog
  rw [map_sub] at hc
  apply Subtype.ext
  exact sub_eq_zero.mp hc

end
end JoshiTeich.Act1Scene1.LocalPadicLog
