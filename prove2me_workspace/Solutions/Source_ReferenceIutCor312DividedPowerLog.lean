import Mathlib.Data.Nat.Choose.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
The divided-power logarithm used for the Kummer and cyclotomic periods.
For the Kummer class built from a compatible root tower, see Joshi III,
“Construction of crystalline, Frobenius invariant Galois cohomology class
associated to a Tate elliptic curve”.
-/

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.DividedPowerLog

open scoped BigOperators

noncomputable section

/-- The factorial of any natural number at least `p * k` is divisible by `p ^ k`. -/
theorem pow_dvd_factorial_of_mul_le {p k n : ℕ} (hp : 0 < p)
    (h : p * k ≤ n) : p ^ k ∣ n.factorial := by
  have hfactorial (j : ℕ) : p ^ j ∣ (p * j).factorial := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, Nat.mul_succ]
      exact (mul_dvd_mul ih (Nat.dvd_factorial hp le_rfl)).trans
        (Nat.factorial_mul_factorial_dvd_factorial_add (p * j) p)
  exact (hfactorial k).trans (Nat.factorial_dvd_factorial h)

variable {R : Type*} [CommRing R]

/-- Index `n` represents degree `n + 1` in the logarithm series with
divided powers `γ`. -/
def logTerm (γ : ℕ → R) (n : ℕ) : R :=
  (-1 : R) ^ n * (n.factorial : R) * γ (n + 1)

/-- The integral coefficient satisfies the ordinary logarithm identity after
multiplication by the degree. -/
theorem natCast_succ_mul_logTerm (γ : ℕ → R) {x : R} (n : ℕ)
    (hγ : ((n + 1).factorial : R) * γ (n + 1) = x ^ (n + 1)) :
    ((n + 1 : ℕ) : R) * logTerm γ n = (-1 : R) ^ n * x ^ (n + 1) := by
  have hfactorial := hγ
  rw [Nat.factorial_succ, Nat.cast_mul] at hfactorial
  calc
    _ = (-1 : R) ^ n *
        (((n + 1 : ℕ) : R) * (n.factorial : R) * γ (n + 1)) := by
      unfold logTerm
      ac_rfl
    _ = _ := by rw [hfactorial]

/-- The first `N` terms of the integral divided-power logarithm. -/
def logPartialSum (γ : ℕ → R) (N : ℕ) : R :=
  ∑ n ∈ Finset.range N, logTerm γ n

/-- In degrees at least `p * k + 1`, every term vanishes modulo `I ^ k`
for an ideal `I` containing the natural number `p`. -/
theorem logTerm_mem_pow (I : Ideal R) {p k n : ℕ} (hp : 0 < p) (hpI : (p : R) ∈ I)
    (γ : ℕ → R) (h : p * k ≤ n) : logTerm γ n ∈ I ^ k := by
  obtain ⟨d, hd⟩ := pow_dvd_factorial_of_mul_le hp h
  have hcast : (n.factorial : R) = (p : R) ^ k * (d : R) := by
    simpa only [Nat.cast_mul, Nat.cast_pow] using congrArg (fun a : ℕ => (a : R)) hd
  have hcoeff : (n.factorial : R) ∈ I ^ k := by
    rw [hcast]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hpI k)
  unfold logTerm
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hcoeff)

/-- Once the truncation has at least `p * k` terms, adding more terms
preserves its residue modulo `I ^ k`. -/
theorem quotient_logPartialSum_eq (I : Ideal R) {p : ℕ} (hp : 0 < p) (hpI : (p : R) ∈ I)
    (γ : ℕ → R) {k N M : ℕ} (hkN : p * k ≤ N) (hNM : N ≤ M) :
    Ideal.Quotient.mk (I ^ k) (logPartialSum γ N) =
      Ideal.Quotient.mk (I ^ k) (logPartialSum γ M) := by
  simp only [logPartialSum, map_sum]
  apply Finset.sum_subset (Finset.range_mono hNM)
  intro n _ hnN
  have hNn : N ≤ n := by simpa only [Finset.mem_range, not_lt] using hnN
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (logTerm_mem_pow I hp hpI γ (hkN.trans hNn))

private def logCauchySequence (p : ℕ) (hp : 0 < p) (γ : ℕ → R) :
    AdicCompletion.AdicCauchySequence (Ideal.span {(p : R)}) R := by
  have hpI : (p : R) ∈ Ideal.span {(p : R)} := Ideal.subset_span (Set.mem_singleton _)
  refine ⟨fun k => logPartialSum γ (p * k), ?_⟩
  intro m n hmn
  simpa only [SModEq.def, smul_eq_mul, Ideal.mul_top, Ideal.Quotient.mk_eq_mk] using
    (quotient_logPartialSum_eq (Ideal.span {(p : R)}) hp hpI γ
      (k := m) (N := p * m) (M := p * n) le_rfl (Nat.mul_le_mul_left p hmn))

/-- For divided powers `γ n` of `x`, this compatible family of residues
represents the logarithm of `1 + x`. -/
def log (p : ℕ) (hp : 0 < p) (γ : ℕ → R) :
    AdicCompletion (Ideal.span {(p : R)}) R :=
  AdicCompletion.mk (Ideal.span {(p : R)}) R (logCauchySequence p hp γ)

/-- Every sufficiently long truncation represents the claimed residue of the
completed logarithm, with the explicit cutoff `p * k`. -/
theorem eval_log_of_le (p : ℕ) (hp : 0 < p) (γ : ℕ → R)
    {k N : ℕ} (hN : p * k ≤ N) :
    AdicCompletion.evalₐ (Ideal.span {(p : R)}) k (log p hp γ) =
      Ideal.Quotient.mk ((Ideal.span {(p : R)}) ^ k) (logPartialSum γ N) := by
  rw [log, AdicCompletion.evalₐ_mk]
  change Ideal.Quotient.mk _ (logPartialSum γ (p * k)) =
    Ideal.Quotient.mk _ (logPartialSum γ N)
  exact quotient_logPartialSum_eq _ hp (Ideal.subset_span (Set.mem_singleton _))
    γ le_rfl hN

end

end JoshiTeich.Act1Scene1.DividedPowerLog
