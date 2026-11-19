import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Weierstrass function bounds for complex lattice torsion

The estimates are those of `Heights/TorsionArchimedean.lean` at
`721496ca4c158e511d25d8ccf6bfe8503eda73c1`. The period lattice and the
Weierstrass function are Mathlib's `PeriodPair.lattice` and `PeriodPair.weierstrassP`.
-/

set_option autoImplicit false

namespace AbcAdaptation.Reference.Heights

open scoped UpperHalfPlane

/-- The period basis ordered as `(τ, 1)`. -/
noncomputable def periodPair (τ : ℍ) : PeriodPair where
  ω₁ := τ
  ω₂ := 1
  indep := LinearIndependent.pair_iff.mpr fun a b h => by
    have him : a * τ.im = 0 := by
      simpa [Complex.real_smul, Complex.mul_im] using congrArg Complex.im h
    have ha : a = 0 := (mul_eq_zero.mp him).resolve_right τ.im_pos.ne'
    subst a
    exact ⟨rfl, by simpa using congrArg Complex.re h⟩

theorem norm_mul_add_sq_ge {τ : ℍ} (hτ : τ ∈ ModularGroup.fd) (a b : ℝ) :
    (a ^ 2 + b ^ 2) / 2 ≤ ‖(a : ℂ) * τ + b‖ ^ 2 := by
  obtain ⟨hτnorm, hτre⟩ := hτ
  change |(τ : ℂ).re| ≤ 1 / 2 at hτre
  have hre : |2 * (τ : ℂ).re| ≤ 1 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith only [hτre]
  have hcross : -(|a| * |b|) ≤ (2 * (τ : ℂ).re) * (a * b) := by
    have h : |(2 * (τ : ℂ).re) * (a * b)| ≤ |a| * |b| := by
      rw [abs_mul, abs_mul a b]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hre (mul_nonneg (abs_nonneg a) (abs_nonneg b))
    exact (neg_le_neg h).trans (neg_abs_le _)
  have hnorm :
      ‖(a : ℂ) * τ + b‖ ^ 2 =
        a ^ 2 * Complex.normSq τ + (2 * (τ : ℂ).re) * (a * b) + b ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_im, Complex.mul_im]
    ring
  rw [hnorm]
  nlinarith only [hcross, sq_nonneg (|a| - |b|), sq_abs a, sq_abs b,
    mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hτnorm)]

/-- The sum of the inverse cubes of the sup norms of the nonzero integer pairs. -/
noncomputable def latticeSumThree : ℝ := ∑' v : Fin 2 → ℤ, ‖v‖ ^ (-3 : ℝ)

private theorem summable_inverse_cube : Summable fun v : Fin 2 → ℤ => ‖v‖ ^ (-3 : ℝ) :=
  EisensteinSeries.summable_one_div_norm_rpow (by norm_num)

theorem latticeSumThree_nonneg : 0 ≤ latticeSumThree :=
  tsum_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _

private lemma one_le_abs_intCast {m : ℤ} (hm : m ≠ 0) : (1 : ℝ) ≤ |(m : ℝ)| := by
  exact_mod_cast Int.one_le_abs hm

private lemma half_le_abs_sub {a s m : ℝ} (ha : |a| ≤ 1 / 2) (hs : 1 ≤ s) (hm : |m| = s) :
    s / 2 ≤ |a - m| := by
  have h := abs_sub_abs_le_abs_sub m a
  rw [hm, abs_sub_comm m a] at h
  linarith only [h, hs, ha]

private lemma max_abs_sq_le (a b : ℝ) : (max |a| |b|) ^ 2 ≤ a ^ 2 + b ^ 2 := by
  rcases le_total |a| |b| with hab | hba
  · rw [max_eq_right hab, sq_abs]
    exact le_add_of_nonneg_left (sq_nonneg a)
  · rw [max_eq_left hba, sq_abs]
    exact le_add_of_nonneg_right (sq_nonneg b)

private theorem norm_weierstrass_summand_le {τ : ℍ} (hτ : τ ∈ ModularGroup.fd)
    {a b : ℝ} (ha : |a| ≤ 1 / 2) (hb : |b| ≤ 1 / 2)
    {m n : ℤ} (hmn : m ≠ 0 ∨ n ≠ 0) :
    let z := (a : ℂ) * τ + b
    let w := (m : ℂ) * τ + n
    ‖1 / (z - w) ^ 2 - 1 / w ^ 2‖ ≤
      80 * ‖(τ : ℂ)‖ ^ 2 * (max |(m : ℝ)| |(n : ℝ)|) ^ (-3 : ℝ) := by
  let z := (a : ℂ) * τ + b
  let w := (m : ℂ) * τ + n
  let s := max |(m : ℝ)| |(n : ℝ)|
  change ‖1 / (z - w) ^ 2 - 1 / w ^ 2‖ ≤ 80 * ‖(τ : ℂ)‖ ^ 2 * s ^ (-3 : ℝ)
  have hs : 1 ≤ s := hmn.elim
    (fun hm => (one_le_abs_intCast hm).trans (le_max_left _ _))
    (fun hn => (one_le_abs_intCast hn).trans (le_max_right _ _))
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have hτnorm : 1 ≤ ‖(τ : ℂ)‖ := by
    have h := hτ.1
    rw [Complex.normSq_eq_norm_sq] at h
    exact le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) (norm_nonneg _)
      (by simpa only [one_pow] using h)
  have hw : s ^ 2 / 2 ≤ ‖w‖ ^ 2 := by
    have h := norm_mul_add_sq_ge hτ (m : ℝ) (n : ℝ)
    push_cast at h
    exact ((div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
      (max_abs_sq_le (m : ℝ) (n : ℝ))).trans h
  have hwz : s ^ 2 / 8 ≤ ‖z - w‖ ^ 2 := by
    have hmax : s / 2 ≤ max |a - (m : ℝ)| |b - (n : ℝ)| := by
      rcases le_total |(m : ℝ)| |(n : ℝ)| with h | h
      · exact (half_le_abs_sub hb hs (max_eq_right h).symm).trans (le_max_right _ _)
      · exact (half_le_abs_sub ha hs (max_eq_left h).symm).trans (le_max_left _ _)
    have hsq := (pow_le_pow_left₀ (show 0 ≤ s / 2 by positivity) hmax 2).trans
      (max_abs_sq_le (a - m) (b - n))
    have h := norm_mul_add_sq_ge hτ (a - m) (b - n)
    have heq : z - w = ((a - m : ℝ) : ℂ) * τ + ((b - n : ℝ) : ℂ) := by
      dsimp [z, w]
      push_cast
      ring
    rw [heq]
    linarith only [hsq, h]
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    nlinarith only [hw, sq_pos_of_pos hs0]
  have hwz0 : z - w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hwz
    nlinarith only [hwz, sq_pos_of_pos hs0]
  have hzup : ‖z‖ ≤ ‖(τ : ℂ)‖ := by
    calc
      ‖z‖ ≤ |a| * ‖(τ : ℂ)‖ + |b| := by
        simpa [z, norm_mul, Complex.norm_real] using norm_add_le ((a : ℂ) * τ) (b : ℂ)
      _ ≤ 1 / 2 * ‖(τ : ℂ)‖ + 1 / 2 :=
        add_le_add (mul_le_mul_of_nonneg_right ha (norm_nonneg _)) hb
      _ ≤ ‖(τ : ℂ)‖ := by linarith only [hτnorm]
  have hwup : ‖w‖ ≤ 2 * s * ‖(τ : ℂ)‖ := by
    calc
      ‖w‖ ≤ |(m : ℝ)| * ‖(τ : ℂ)‖ + |(n : ℝ)| := by
        simpa [w, norm_mul, Complex.norm_intCast] using norm_add_le ((m : ℂ) * τ) (n : ℂ)
      _ ≤ s * ‖(τ : ℂ)‖ + s * ‖(τ : ℂ)‖ :=
        add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
          ((le_max_right _ _).trans (le_mul_of_one_le_right hs0.le hτnorm))
      _ = _ := by ring
  have hnum : ‖2 * w - z‖ ≤ 5 * s * ‖(τ : ℂ)‖ := by
    calc
      ‖2 * w - z‖ ≤ 2 * ‖w‖ + ‖z‖ := by
        simpa [norm_mul] using norm_sub_le (2 * w) z
      _ ≤ 2 * (2 * s * ‖(τ : ℂ)‖) + s * ‖(τ : ℂ)‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hwup (by norm_num))
          (hzup.trans (le_mul_of_one_le_left (norm_nonneg _) hs))
      _ = _ := by ring
  have hden : s ^ 4 / 16 ≤ ‖z - w‖ ^ 2 * ‖w‖ ^ 2 := by
    calc
      s ^ 4 / 16 = (s ^ 2 / 8) * (s ^ 2 / 2) := by ring
      _ ≤ _ := mul_le_mul hwz hw (by positivity) (sq_nonneg _)
  have hf : 1 / (z - w) ^ 2 - 1 / w ^ 2 = z * (2 * w - z) / ((z - w) ^ 2 * w ^ 2) := by
    field_simp [hw0, hwz0]
    ring
  rw [hf, norm_div, norm_mul, norm_mul, norm_pow, norm_pow,
    Real.rpow_neg hs0.le, show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast,
    div_le_iff₀ (by positivity)]
  calc
    ‖z‖ * ‖2 * w - z‖ ≤ ‖(τ : ℂ)‖ * (5 * s * ‖(τ : ℂ)‖) := by gcongr
    _ = 80 * ‖(τ : ℂ)‖ ^ 2 * (s ^ 3)⁻¹ * (s ^ 4 / 16) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)

private theorem norm_weierstrassP_on_parallelogram {τ : ℍ} (hτ : τ ∈ ModularGroup.fd)
    {a b : ℝ} (ha : |a| ≤ 1 / 2) (hb : |b| ≤ 1 / 2) :
    ‖(periodPair τ).weierstrassP ((a : ℂ) * τ + b)‖ ≤
      1 / ‖(a : ℂ) * τ + b‖ ^ 2 + 80 * ‖(τ : ℂ)‖ ^ 2 * latticeSumThree := by
  classical
  let L := periodPair τ
  let z := (a : ℂ) * τ + b
  let e := (L.latticeEquivProd.trans (LinearEquiv.finTwoArrow ℤ ℤ).symm).toEquiv
  have he0 : e 0 = 0 := map_zero (L.latticeEquivProd.trans (LinearEquiv.finTwoArrow ℤ ℤ).symm)
  let f (l : L.lattice) := 1 / (z - l) ^ 2 - 1 / (l : ℂ) ^ 2
  let pole (l : L.lattice) := if l = 0 then 1 / ‖z‖ ^ 2 else 0
  let tail (l : L.lattice) := 80 * ‖(τ : ℂ)‖ ^ 2 * ‖e l‖ ^ (-3 : ℝ)
  have hpole : Summable pole := by
    apply summable_of_hasFiniteSupport
    exact (Set.finite_singleton 0).subset (fun l hl => by
      by_contra h
      exact hl (if_neg h))
  have htail : Summable tail := (e.summable_iff.mpr summable_inverse_cube).mul_left _
  have hbound (l : L.lattice) : ‖f l‖ ≤ pole l + tail l := by
    by_cases h0 : l = 0
    · subst l
      simp [f, pole, tail, he0, norm_pow]
    · let v := e l
      have hv : v ≠ 0 := fun h => h0 (e.injective (h.trans he0.symm))
      have hcoords : (l : ℂ) = (v 0 : ℂ) * τ + (v 1 : ℂ) := by
        change (l : ℂ) = ((L.latticeEquivProd l).1 : ℂ) * τ + ((L.latticeEquivProd l).2 : ℂ)
        have h := L.latticeEquiv_symm_apply (L.latticeEquivProd l)
        rw [LinearEquiv.symm_apply_apply] at h
        simpa only [L, periodPair, mul_one] using h
      have hpair : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
        by_contra! h
        exact hv (funext (Fin.forall_fin_two.mpr h))
      have hnorm : ‖v‖ = max |(v 0 : ℝ)| |(v 1 : ℝ)| := by
        rw [EisensteinSeries.norm_eq_max_natAbs, Nat.cast_max, Nat.cast_natAbs, Nat.cast_natAbs,
          Int.cast_abs, Int.cast_abs]
      dsimp only [f, pole, tail]
      rw [if_neg h0, zero_add, ← show v = e l from rfl, hcoords, hnorm]
      exact norm_weierstrass_summand_le hτ ha hb hpair
  have hsum := hpole.add htail
  have hnorm : Summable fun l => ‖f l‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hsum
  calc
    ‖L.weierstrassP z‖ = ‖∑' l, f l‖ := rfl
    _ ≤ ∑' l, ‖f l‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' l, (pole l + tail l) := hnorm.tsum_le_tsum hbound hsum
    _ = _ := by
      rw [hpole.tsum_add htail]
      simp only [pole, tail, tsum_ite_eq, tsum_mul_left]
      rw [e.tsum_eq (fun v => ‖v‖ ^ (-3 : ℝ))]
      rfl

/-- On the modular fundamental domain, a nonzero lattice class killed by `N`
has Weierstrass function norm at most `2 N² + 80 ‖τ‖² S`. -/
theorem norm_weierstrassP_torsion_le {τ : ℍ} (hτ : τ ∈ ModularGroup.fd) {N : ℕ}
    (hN : 1 ≤ N) {z : ℂ} (hNz : (N : ℂ) * z ∈ (periodPair τ).lattice)
    (hz : z ∉ (periodPair τ).lattice) :
    ‖(periodPair τ).weierstrassP z‖ ≤ 2 * N ^ 2 + 80 * ‖(τ : ℂ)‖ ^ 2 * latticeSumThree := by
  obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.mp hNz
  change (m : ℂ) * τ + (n : ℂ) * 1 = (N : ℂ) * z at hmn
  rw [mul_one] at hmn
  have hNℝ : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N from hN)
  have hNℂ : (N : ℂ) ≠ 0 := by exact_mod_cast hNℝ.ne'
  let k := round ((m : ℝ) / N)
  let k' := round ((n : ℝ) / N)
  let p : ℤ := m - N * k
  let q : ℤ := n - N * k'
  let a : ℝ := (p : ℝ) / N
  let b : ℝ := (q : ℝ) / N
  have ha_eq : a = (m : ℝ) / N - k := by dsimp [a, p]; push_cast; field_simp
  have hb_eq : b = (n : ℝ) / N - k' := by dsimp [b, q]; push_cast; field_simp
  have ha : |a| ≤ 1 / 2 := ha_eq ▸ abs_sub_round ((m : ℝ) / N)
  have hb : |b| ≤ 1 / 2 := hb_eq ▸ abs_sub_round ((n : ℝ) / N)
  let u := ((a : ℂ) * τ + b)
  let w := ((k : ℂ) * τ + k')
  have hw : w ∈ (periodPair τ).lattice :=
    PeriodPair.mem_lattice.mpr ⟨k, k', by change (k : ℂ) * τ + (k' : ℂ) * 1 = w; rw [mul_one]⟩
  have hzw : z = u + w := by
    apply mul_left_cancel₀ hNℂ
    rw [← hmn]
    dsimp [u, w]
    rw [ha_eq, hb_eq]
    push_cast
    field_simp
    ring
  have hnotzero : p ≠ 0 ∨ q ≠ 0 := by
    by_contra! h
    apply hz
    simpa [hzw, u, a, b, h.1, h.2] using hw
  have hpq : (1 : ℝ) ≤ (p : ℝ) ^ 2 + (q : ℝ) ^ 2 := by
    rcases hnotzero with hp | hq
    · have h := pow_le_pow_left₀ zero_le_one (one_le_abs_intCast hp) 2
      rw [one_pow, sq_abs] at h
      exact h.trans (le_add_of_nonneg_right (sq_nonneg _))
    · have h := pow_le_pow_left₀ zero_le_one (one_le_abs_intCast hq) 2
      rw [one_pow, sq_abs] at h
      exact h.trans (le_add_of_nonneg_left (sq_nonneg _))
  have hden : 1 / (2 * (N : ℝ) ^ 2) ≤ ‖u‖ ^ 2 := by
    have h := norm_mul_add_sq_ge hτ a b
    refine le_trans ?_ h
    dsimp [a, b]
    rw [div_pow, div_pow, ← add_div, div_div]
    rw [mul_comm ((N : ℝ) ^ 2) 2]
    exact div_le_div_of_nonneg_right hpq (by positivity)
  have hu : 0 < ‖u‖ ^ 2 := lt_of_lt_of_le (by positivity) hden
  have hinv : 1 / ‖u‖ ^ 2 ≤ 2 * (N : ℝ) ^ 2 := by
    rw [div_le_iff₀ hu]
    exact ((div_le_iff₀ (by positivity : 0 < 2 * (N : ℝ) ^ 2)).mp hden).trans_eq (mul_comm _ _)
  have hperiod : (periodPair τ).weierstrassP z = (periodPair τ).weierstrassP u := by
    rw [hzw]
    exact (periodPair τ).weierstrassP_add_coe u ⟨w, hw⟩
  rw [hperiod]
  exact (norm_weierstrassP_on_parallelogram hτ ha hb).trans (add_le_add hinv le_rfl)

end AbcAdaptation.Reference.Heights
