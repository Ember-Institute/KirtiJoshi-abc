import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy

/-!
source-id: JT-SCENE1-MULTIPLICATIVE-NORM-DIVISION-LIMIT
source: Joshi II `se:ff-rings`, passage from finite primitive products
to divisibility in the complete period ring.
fidelity: in a ring with a multiplicative norm, exact quotients of a
fixed element form a Cauchy sequence when their nonzero divisors tend
to a nonzero limit. The proof uses the exact two-denominator difference
identity. Completeness supplies a quotient of the limit.
Original proofs; no reference implementation copied.
boundary: generic Scene1/Derived lemma; the actual product, nonzero
limit and exact finite quotients must be constructed by its consumer.
-/

namespace JoshiTeich.Act1Scene1.MultiplicativeNormDivisionLimit

open Filter
open scoped Topology
variable {R : Type*} [NormedCommRing R] [NormMulClass R]

theorem norm_quotient_sub (a y : ℕ → R) (x : R)
    (ha : ∀ n, a n ≠ 0) (hxy : ∀ n, a n * y n = x) (n m : ℕ) :
    ‖y n - y m‖ = ‖x‖ * ‖a m - a n‖ / (‖a n‖ * ‖a m‖) := by
  have he : a n * a m * (y n - y m) = x * (a m - a n) := by
    calc
      _ = a m * (a n * y n) - a n * (a m * y m) := by ring
      _ = _ := by rw [hxy n, hxy m]; ring
  have hn := congrArg norm he
  simp only [norm_mul] at hn
  apply (eq_div_iff (mul_ne_zero (norm_ne_zero_iff.mpr (ha n))
    (norm_ne_zero_iff.mpr (ha m)))).mpr
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hn

theorem cauchySeq_quotient (a y : ℕ → R) (x A : R)
    (ha : ∀ n, a n ≠ 0) (hA : A ≠ 0)
    (ht : Tendsto a atTop (𝓝 A)) (hxy : ∀ n, a n * y n = x) : CauchySeq y := by
  have h₁ : Tendsto (fun z : ℕ × ℕ => a z.1) atTop (𝓝 A) :=
    ht.comp (by rw [← prod_atTop_atTop_eq]; exact tendsto_fst)
  have h₂ : Tendsto (fun z : ℕ × ℕ => a z.2) atTop (𝓝 A) :=
    ht.comp (by rw [← prod_atTop_atTop_eq]; exact tendsto_snd)
  have hnum : Tendsto (fun z : ℕ × ℕ => ‖x‖ * ‖a z.2 - a z.1‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, mul_zero] using tendsto_const_nhds.mul (h₂.sub h₁).norm
  have hden := h₁.norm.mul h₂.norm
  have h := hnum.div hden (mul_ne_zero (norm_ne_zero_iff.mpr hA) (norm_ne_zero_iff.mpr hA))
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  have h' : Tendsto (fun z : ℕ × ℕ =>
      ‖x‖ * ‖a z.2 - a z.1‖ / (‖a z.1‖ * ‖a z.2‖)) atTop (𝓝 0) := by
    have heq : (fun z : ℕ × ℕ =>
        ‖x‖ * ‖a z.2 - a z.1‖ / (‖a z.1‖ * ‖a z.2‖)) =
        (fun z : ℕ × ℕ => ‖x‖ * ‖a z.2 - a z.1‖) /
          (fun z => ‖a z.1‖ * ‖a z.2‖) := by
      funext z
      rfl
    simpa only [← heq, zero_div] using h
  simpa only [dist_eq_norm, norm_quotient_sub a y x ha hxy] using h'

theorem exists_quotient_limit [CompleteSpace R] (a y : ℕ → R) (x A : R)
    (ha : ∀ n, a n ≠ 0) (hA : A ≠ 0)
    (ht : Tendsto a atTop (𝓝 A)) (hxy : ∀ n, a n * y n = x) :
    ∃ Y : R, Tendsto y atTop (𝓝 Y) ∧ A * Y = x := by
  obtain ⟨Y, hY⟩ := cauchySeq_tendsto_of_complete (cauchySeq_quotient a y x A ha hA ht hxy)
  refine ⟨Y, hY, ?_⟩
  have hm := ht.mul hY
  simp only [hxy] at hm
  exact tendsto_nhds_unique hm tendsto_const_nhds

end JoshiTeich.Act1Scene1.MultiplicativeNormDivisionLimit
