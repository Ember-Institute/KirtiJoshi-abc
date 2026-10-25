import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedDigits
import Mathlib.Data.Finset.Max

/-!
source-id: JT-SCENE1-WITT-WEIGHTED-DIGIT-ADDITION
source: the Teichmuller expansions underlying Joshi II `se:ff-rings` and
`pr:teichmuller-lift-A/B`; actual truncated Witt ring homomorphisms.
fidelity: controls carries by lifting finite coefficient heads to the
norm unit-ball subring. Finite maxima and Teichmuller scaling then prove
the ultrametric inequality for the extended weighted digit supremum.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; the unit-ball subring is explicit and is supplied
by the actual tilt integers in the consumer. No multiplication estimate
or completed Frechet period-ring identification is asserted.
-/

namespace JoshiTeich.Act1Scene1.WittWeightedDigitAddition

open WittTeichmullerExpansion WittWeightedDigits
open scoped ENNReal
noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {F : Type*} [NormedField F] [CharP F p] [PerfectRing F p]

private def liftHead (O : Subring F) (x : WittVector p F) (n : ℕ)
    (h : ∀ i ≤ n, x.coeff i ∈ O) : WittVector p O :=
  WittVector.mk p (fun i => if hi : i ≤ n then ⟨x.coeff i, h i hi⟩ else 0)

omit [CharP F p] [PerfectRing F p] in
private theorem truncate_liftHead (O : Subring F) (x : WittVector p F) (n : ℕ)
    (h : ∀ i ≤ n, x.coeff i ∈ O) :
    (WittVector.map O.subtype (liftHead p O x n h)).truncate (n + 1) = x.truncate (n + 1) := by
  ext i
  simp [WittVector.coeff_truncate, WittVector.map_coeff, liftHead,
    Nat.le_of_lt_succ i.isLt]

omit [CharP F p] [PerfectRing F p] in
theorem coeff_add_mem_of_head (O : Subring F) (x y : WittVector p F) (n : ℕ)
    (hx : ∀ i ≤ n, x.coeff i ∈ O) (hy : ∀ i ≤ n, y.coeff i ∈ O) :
    (x + y).coeff n ∈ O := by
  let a := liftHead p O x n hx
  let b := liftHead p O y n hy
  have ht : (WittVector.map O.subtype (a + b)).truncate (n + 1) =
      (x + y).truncate (n + 1) := by
    simpa only [map_add] using congrArg₂ (· + ·)
      (truncate_liftHead p O x n hx) (truncate_liftHead p O y n hy)
  have hc := congrArg (fun z : TruncatedWittVector p (n + 1) F =>
    z.coeff ⟨n, Nat.lt_succ_self n⟩) ht
  simp only [WittVector.coeff_truncate, WittVector.map_coeff] at hc
  rw [← hc]
  exact ((a + b).coeff n).property

theorem norm_digits_add_le_one (O : Subring F) (hO : ∀ a : F, a ∈ O ↔ ‖a‖ ≤ 1)
    (x y : WittVector p F) (n : ℕ)
    (hx : ∀ i ≤ n, ‖digits p x i‖ ≤ 1) (hy : ∀ i ≤ n, ‖digits p y i‖ ≤ 1) :
    ‖digits p (x + y) n‖ ≤ 1 := by
  have hc := fun (z : WittVector p F) =>
    (expands_iff_coeff p z (digits p z)).mp (expands_digits p z)
  have hxi : ∀ i ≤ n, x.coeff i ∈ O := by
    intro i hi
    apply (hO _).mpr
    rw [hc x i, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hx i hi)
  have hyi : ∀ i ≤ n, y.coeff i ∈ O := by
    intro i hi
    apply (hO _).mpr
    rw [hc y i, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hy i hi)
  have hsum := (hO _).mp (coeff_add_mem_of_head p O x y n hxi hyi)
  rw [hc (x + y) n, norm_pow] at hsum
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _)
    (pow_ne_zero n (Fact.out : p.Prime).ne_zero)).mp hsum

theorem norm_digits_add_le_of_nonzero (O : Subring F)
    (hO : ∀ a : F, a ∈ O ↔ ‖a‖ ≤ 1) (r : F) (hr : r ≠ 0)
    (x y : WittVector p F) (n : ℕ)
    (hx : ∀ i ≤ n, ‖digits p x i‖ ≤ ‖r‖)
    (hy : ∀ i ≤ n, ‖digits p y i‖ ≤ ‖r‖) :
    ‖digits p (x + y) n‖ ≤ ‖r‖ := by
  have hri : ‖r‖ ≠ 0 := norm_ne_zero_iff.mpr hr
  have hscale : ∀ z : WittVector p F, (∀ i ≤ n, ‖digits p z i‖ ≤ ‖r‖) →
      ∀ i ≤ n, ‖digits p (WittVector.teichmuller p r⁻¹ * z) i‖ ≤ 1 := by
    intro z hz i hi
    rw [digits_teichmuller_mul, norm_mul, norm_inv]
    exact (mul_le_mul_of_nonneg_left (hz i hi) (inv_nonneg.mpr (norm_nonneg r))).trans
      (inv_mul_cancel₀ hri).le
  have h := norm_digits_add_le_one p O hO
    (WittVector.teichmuller p r⁻¹ * x) (WittVector.teichmuller p r⁻¹ * y) n
    (hscale x hx) (hscale y hy)
  rw [← mul_add, digits_teichmuller_mul, norm_mul, norm_inv] at h
  have hm := mul_le_mul_of_nonneg_left h (norm_nonneg r)
  rwa [← mul_assoc, mul_inv_cancel₀ hri, one_mul, mul_one] at hm

theorem digits_add_eq_zero_of_head (x y : WittVector p F) (n : ℕ)
    (hx : ∀ i ≤ n, digits p x i = 0) (hy : ∀ i ≤ n, digits p y i = 0) :
    digits p (x + y) n = 0 := by
  have htr : ∀ z : WittVector p F, (∀ i ≤ n, digits p z i = 0) →
      z.truncate (n + 1) = 0 := by
    intro z hz
    ext i
    rw [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero,
      (expands_iff_coeff p z (digits p z)).mp (expands_digits p z) i.val,
      hz i.val (Nat.le_of_lt_succ i.isLt)]
    exact zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have ht : (x + y).truncate (n + 1) = 0 := by
    rw [map_add, htr x hx, htr y hy, add_zero]
  have hc := congrArg (fun z : TruncatedWittVector p (n + 1) F =>
    z.coeff ⟨n, Nat.lt_succ_self n⟩) ht
  simp only [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero] at hc
  simp [digits, hc]

theorem value_add_le_max (O : Subring F) (hO : ∀ a : F, a ∈ O ↔ ‖a‖ ≤ 1)
    (ρ : ℝ≥0∞) (hρ : ρ ≤ 1) (x y : WittVector p F) :
    value p ρ (x + y) ≤ max (value p ρ x) (value p ρ y) := by
  classical
  apply iSup_le
  intro n
  let s := (Finset.Iic n).image (digits p x) ∪ (Finset.Iic n).image (digits p y)
  have hs : s.Nonempty := by
    refine ⟨digits p x 0, ?_⟩
    exact Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n), rfl⟩)
  obtain ⟨r, hrmem, hrmax⟩ := Finset.exists_max_image s (fun a : F => ‖a‖) hs
  have hx : ∀ i ≤ n, ‖digits p x i‖ ≤ ‖r‖ := by
    intro i hi
    exact hrmax _ (Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨i, Finset.mem_Iic.mpr hi, rfl⟩))
  have hy : ∀ i ≤ n, ‖digits p y i‖ ≤ ‖r‖ := by
    intro i hi
    exact hrmax _ (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨i, Finset.mem_Iic.mpr hi, rfl⟩))
  by_cases hr : r = 0
  · have hdx : ∀ i ≤ n, digits p x i = 0 := by
      intro i hi
      apply norm_eq_zero.mp
      exact le_antisymm (by simpa only [hr, norm_zero] using hx i hi) (norm_nonneg _)
    have hdy : ∀ i ≤ n, digits p y i = 0 := by
      intro i hi
      apply norm_eq_zero.mp
      exact le_antisymm (by simpa only [hr, norm_zero] using hy i hi) (norm_nonneg _)
    rw [digits_add_eq_zero_of_head p x y n hdx hdy, norm_zero, ENNReal.ofReal_zero, zero_mul]
    exact bot_le
  · have hadd := norm_digits_add_le_of_nonzero p O hO r hr x y n hx hy
    rcases Finset.mem_union.mp hrmem with hxmem | hymem
    · obtain ⟨i, hi, hri⟩ := Finset.mem_image.mp hxmem
      rw [← hri] at hadd
      exact (mul_le_mul (ENNReal.ofReal_le_ofReal hadd)
        (pow_le_pow_of_le_one bot_le hρ (Finset.mem_Iic.mp hi)) bot_le bot_le).trans
        ((term_le_value p ρ x i).trans (le_max_left _ _))
    · obtain ⟨i, hi, hri⟩ := Finset.mem_image.mp hymem
      rw [← hri] at hadd
      exact (mul_le_mul (ENNReal.ofReal_le_ofReal hadd)
        (pow_le_pow_of_le_one bot_le hρ (Finset.mem_Iic.mp hi)) bot_le bot_le).trans
        ((term_le_value p ρ y i).trans (le_max_right _ _))

end
end JoshiTeich.Act1Scene1.WittWeightedDigitAddition
