import ArithmeticTeichmullerSpaces.Act1Scene1.LocalPrincipalUnitPadicPower
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerTowerPowers

/-!
source-id: JT-SCENE1-KUMMER-PADIC-POWER-TOWER
source: actual principal-unit integer-power limits and compatible Kummer
roots; Joshi III 3190--3226.
fidelity: constructs compatible base-field correction limits, then a root
tower for the actual p-adic power. Its Galois ratio is the p-adic scalar
power of the original cocycle. No continuity on an algebraic closure or
completion of it is assumed. H1e/BK identification remains open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer.PadicPowerTower
open Filter Topology
open scoped Valued
universe u v
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def tailExponent (r : ℤ_[p]) (N m : ℕ) : ℕ :=
  (r.appr (N + m) - r.appr N) / p ^ N

theorem mul_tailExponent (r : ℤ_[p]) (N m : ℕ) :
    p ^ N * tailExponent r N m = r.appr (N + m) - r.appr N :=
  Nat.mul_div_cancel' (r.dvd_appr_sub_appr N (N + m) (Nat.le_add_right N m))

theorem tailExponent_mono (r : ℤ_[p]) (N : ℕ) : Monotone (tailExponent r N) := by
  intro m n hmn
  unfold tailExponent
  exact Nat.div_le_div_right (Nat.sub_le_sub_right (r.appr_mono (Nat.add_le_add_left hmn N)) _)

theorem dvd_tailExponent_sub (r : ℤ_[p]) (N m n : ℕ) (hmn : m ≤ n) :
    p ^ m ∣ tailExponent r N n - tailExponent r N m := by
  obtain ⟨d, hd⟩ := r.dvd_appr_sub_appr (N + m) (N + n) (Nat.add_le_add_left hmn N)
  refine ⟨d, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : p.Prime).pos N)
  rw [Nat.mul_sub_left_distrib, mul_tailExponent, mul_tailExponent,
    ← mul_assoc, ← pow_add, ← hd]
  have h0 := r.appr_mono (Nat.le_add_right N m)
  omega

theorem tailExponent_step (r : ℤ_[p]) (N m : ℕ) :
    tailExponent r N (m + 1) = tailExponent r N 1 + p * tailExponent r (N + 1) m := by
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : p.Prime).pos N)
  rw [Nat.mul_add, mul_tailExponent, mul_tailExponent,
    ← mul_assoc, ← pow_succ, mul_tailExponent]
  have h0 := r.appr_mono (Nat.le_succ N)
  have h1 := r.appr_mono (Nat.le_add_right (N + 1) m)
  have he : N + (m + 1) = (N + 1) + m := by omega
  rw [he]
  simp only [Nat.succ_eq_add_one] at h0
  omega

theorem tailExponent_zero (r : ℤ_[p]) (m : ℕ) : tailExponent r 0 m = r.appr m := by
  have h0 : r.appr 0 = 0 := rfl
  simp only [tailExponent, zero_add, pow_zero, h0, Nat.sub_zero, Nat.div_one]

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
variable [CharZero k] [CompleteSpace k]
variable (hpk : ‖(p : k)‖ < 1) (a : LocalPadicLog.principalUnits (k := k)) (r : ℤ_[p])

include hpk in
theorem tail_powers_cauchy (N : ℕ) :
    CauchySeq (fun m : ℕ => (a.1 : k) ^ tailExponent r N m) := by
  apply cauchySeq_of_le_tendsto_0' (fun m => ‖(a.1 : k) ^ (p ^ m) - 1‖)
  · intro m n hmn
    exact LocalPadicLog.principal_pow_dist_le_of_dvd a.2
      (tailExponent_mono r N hmn) (dvd_tailExponent_sub r N m n hmn)
  · simpa only [norm_zero] using
      (LocalPadicLog.tendsto_principal_prime_power_sub_one (Fact.out : p.Prime) hpk a.2).norm

include hpk in
private theorem tail_limit_exists (N : ℕ) :
    ∃ b : k, Tendsto (fun m : ℕ => (a.1 : k) ^ tailExponent r N m) atTop (𝓝 b) :=
  cauchySeq_tendsto_of_complete (tail_powers_cauchy hpk a r N)

def correction (N : ℕ) : k := Classical.choose (tail_limit_exists hpk a r N)

theorem tendsto_correction (N : ℕ) :
    Tendsto (fun m : ℕ => (a.1 : k) ^ tailExponent r N m) atTop
      (𝓝 (correction hpk a r N)) := Classical.choose_spec (tail_limit_exists hpk a r N)

theorem correction_principal (N : ℕ) : ‖correction hpk a r N - 1‖ < 1 := by
  have hle : ‖correction hpk a r N - 1‖ ≤ ‖(a.1 : k) - 1‖ :=
    le_of_tendsto ((tendsto_correction hpk a r N).sub_const 1).norm
      (Filter.Eventually.of_forall fun m => LocalPadicLog.norm_principal_pow_sub_one_le a.2 _)
  exact hle.trans_lt a.2

theorem correction_zero : correction hpk a r 0 =
    ((LocalPadicLog.principalPadicPower hpk a r).1 : k) := by
  apply tendsto_nhds_unique (tendsto_correction hpk a r 0)
  simpa only [tailExponent_zero] using LocalPadicLog.tendsto_principalPadicPower hpk a r

/-- This recurrence supplies compatible roots, not just separate roots at each level. -/
theorem correction_step (N : ℕ) :
    correction hpk a r N = (a.1 : k) ^ tailExponent r N 1 * correction hpk a r (N + 1) ^ p := by
  have hl := (tendsto_correction hpk a r N).comp (tendsto_add_atTop_nat 1)
  have hr := ((tendsto_correction hpk a r (N + 1)).pow p).const_mul
    ((a.1 : k) ^ tailExponent r N 1)
  apply tendsto_nhds_unique hl
  exact hr.congr fun m => by
    change (a.1 : k) ^ tailExponent r N 1 * ((a.1 : k) ^ tailExponent r (N + 1) m) ^ p =
      (a.1 : k) ^ tailExponent r N (m + 1)
    rw [tailExponent_step r N m, pow_add, ← pow_mul,
      Nat.mul_comm (tailExponent r (N + 1) m) p]

variable {Ω : Type v} [Field Ω] [Algebra k Ω]
variable (R : RootTower (Ω := Ω) p (a.1 : k))

/-- All limiting corrections lie in k; roots in Ω only come from the original tower. -/
def tower : RootTower (Ω := Ω) p ((LocalPadicLog.principalPadicPower hpk a r).1 : k) where
  root N := R.root N ^ r.appr N * algebraMap k Ω (correction hpk a r N)
  root_zero := by
    have h0 : r.appr 0 = 0 := rfl
    rw [h0, pow_zero, one_mul, correction_zero]
  root_succ N := by
    rw [mul_pow, ← pow_mul, mul_comm (r.appr (N + 1)) p, pow_mul, R.root_succ]
    have he : r.appr (N + 1) = r.appr N + p ^ N * tailExponent r N 1 := by
      have h := mul_tailExponent r N 1
      have hle := r.appr_mono (Nat.le_succ N)
      simp only [Nat.succ_eq_add_one] at hle
      omega
    rw [he, pow_add, pow_mul, R.root_pow_eq,
      ← map_pow (algebraMap k Ω) (correction hpk a r (N + 1)) p,
      ← map_pow (algebraMap k Ω) (a.1 : k) (tailExponent r N 1),
      mul_assoc, ← map_mul, ← correction_step]

theorem tower_ratio (σ : Ω ≃ₐ[k] Ω) (N : ℕ) :
    (tower hpk a r R).ratio σ N = R.ratio σ N ^ r.appr N := by
  have hc : algebraMap k Ω (correction hpk a r N) ≠ 0 :=
    (map_ne_zero _).mpr (LocalPadicLog.ne_zero_of_norm_sub_one_lt (correction_principal hpk a r N))
  change σ (R.root N ^ r.appr N * algebraMap k Ω (correction hpk a r N)) /
    (R.root N ^ r.appr N * algebraMap k Ω (correction hpk a r N)) = _
  rw [map_mul, σ.commutes, mul_div_mul_right _ _ hc, map_pow, ← div_pow]
  rfl

theorem tower_cocycle (σ : Ω ≃ₐ[k] Ω) :
    (tower hpk a r R).kummerCocycle (Fact.out : p.Prime).pos
      (LocalPadicLog.ne_zero_of_norm_sub_one_lt (LocalPadicLog.principalPadicPower hpk a r).2) σ =
    LocalKummer.padicPower r (R.kummerCocycle (Fact.out : p.Prime).pos a.1.ne_zero σ) := by
  apply Subtype.ext
  funext N
  apply Units.ext
  change (tower hpk a r R).ratio σ N =
    R.ratio σ N ^ (PadicInt.toZModPow N r).val
  rw [tower_ratio]
  have he : (PadicInt.toZModPow N r).val = r.appr N := by
    change ((r.appr N : ZMod (p ^ N))).val = r.appr N
    exact ZMod.val_natCast_of_lt (r.appr_lt N)
  rw [he]

end
end JoshiTeich.Act1Scene1.LocalKummer.PadicPowerTower
