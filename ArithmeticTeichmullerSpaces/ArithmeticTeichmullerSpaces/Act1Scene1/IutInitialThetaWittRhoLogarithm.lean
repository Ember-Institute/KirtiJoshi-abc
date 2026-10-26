import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittIwasawaLimit

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-RHO-LOGARITHM
source: Joshi II `pr:teichmuller-lift-A`, multiplicative-formal-group
periods; the Iwasawa normalized p-power difference quotient.
fidelity: constructs the actual log(1+x) series on the open unit ball
of each original rho completion and proves its Iwasawa limit formula
by the actual binomial coefficient limit and dominated convergence.
It agrees with the coordinate of the existing common-ring logarithm.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; no exp/log inverse or period representation
is assumed. The original fixed-radius topology is retained. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittRhoLogarithm

open JoshiTeich.Prologue
open InitialThetaWittRhoCompletion (Completed)
open InitialThetaWittAllRadiusPadicScalars InitialThetaWittPadicScalarNorm
open InitialThetaWittLogDenominatorBounds InitialThetaWittLogarithmSeries
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def term (ρ : Radius) (x : Completed D w ρ) (n : ℕ) : Completed D w ρ :=
  logCoefficient D w n • x ^ n

theorem norm_term_le (ρ : Radius) (s : ℕ)
    (hs : ∀ n : ℕ, n ≠ 0 →
      ‖completedPadicMap D w ρ (n : Padic (Arithmetic.residueChar w.1))⁻¹‖ ≤ (n : ℝ) ^ s)
    (x : Completed D w ρ) (n : ℕ) : ‖term D w ρ x n‖ ≤ (n : ℝ) ^ s * ‖x‖ ^ n := by
  rw [term, norm_padic_smul]
  exact mul_le_mul (norm_logCoefficient_le D w ρ s hs n) (norm_pow_le _ _)
    (norm_nonneg _) (pow_nonneg (Nat.cast_nonneg n) s)

theorem summable_norm_term (ρ : Radius) (x : Completed D w ρ) (hx : ‖x‖ < 1) :
    Summable (fun n : ℕ => ‖term D w ρ x n‖) := by
  obtain ⟨s, hs⟩ := exists_polynomial_bound D w ρ
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_le D w ρ s hs x)
    (summable_pow_mul_geometric_of_norm_lt_one s (by simpa only [norm_norm] using hx))

def logOneAdd (ρ : Radius) (x : Completed D w ρ) : Completed D w ρ := ∑' n : ℕ, term D w ρ x n

theorem hasSum_logOneAdd (ρ : Radius) (x : Completed D w ρ) (hx : ‖x‖ < 1) :
    HasSum (term D w ρ x) (logOneAdd D w ρ x) := (summable_norm_term D w ρ x hx).of_norm.hasSum

theorem evaluate_logOneAdd (ρ : Radius) (x : InitialThetaWittAllRadiusCompletion.Carrier D w)
    (hx : ∀ r : Radius, InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w r x < 1) :
    InitialThetaWittAllRadiusCompletion.evaluate D w ρ
        (InitialThetaWittLogarithmSeries.logOneAdd D w x) =
      logOneAdd D w ρ (InitialThetaWittAllRadiusCompletion.evaluate D w ρ x) :=
  InitialThetaWittLogarithmSeries.evaluate_logOneAdd D w ρ x hx

def binomialTerm (ρ : Radius) (x : Completed D w ρ) (m n : ℕ) : Completed D w ρ :=
  PadicBinomialLogCoefficients.coefficient (Padic (Arithmetic.residueChar w.1)) m n • x ^ n

def quotient (ρ : Radius) (x : Completed D w ρ) (k : ℕ) : Completed D w ρ :=
  ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k)⁻¹ •
    ((1 + x) ^ (Arithmetic.residueChar w.1 ^ k) - 1)

theorem binomialTerm_zero_outside (ρ : Radius) (x : Completed D w ρ) (m n : ℕ)
    (hn : n ∉ Finset.range (m + 1)) : binomialTerm D w ρ x m n = 0 := by
  have hmn : m < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self m) (Nat.le_of_not_gt (by simpa using hn))
  simp only [binomialTerm, PadicBinomialLogCoefficients.coefficient, Nat.choose_eq_zero_of_lt hmn,
    Nat.cast_zero, zero_div, ite_self, zero_smul]

theorem binomialTerm_eq (ρ : Radius) (x : Completed D w ρ) (m n : ℕ) :
    binomialTerm D w ρ x m n =
      (m : Padic (Arithmetic.residueChar w.1))⁻¹ •
        ((m.choose n : Padic (Arithmetic.residueChar w.1)) • x ^ n) -
      if n = 0 then (m : Padic (Arithmetic.residueChar w.1))⁻¹ • (1 : Completed D w ρ) else 0 := by
  by_cases hn : n = 0
  · simp [binomialTerm, PadicBinomialLogCoefficients.coefficient, hn]
  · simp only [binomialTerm, PadicBinomialLogCoefficients.coefficient, if_neg hn,
      sub_zero, div_eq_mul_inv, smul_smul]
    rw [mul_comm]

theorem sum_binomialTerm (ρ : Radius) (x : Completed D w ρ) (m : ℕ) :
    (∑ n ∈ Finset.range (m + 1), binomialTerm D w ρ x m n) =
      (m : Padic (Arithmetic.residueChar w.1))⁻¹ • ((1 + x) ^ m - 1) := by
  have hb : (1 + x) ^ m =
      ∑ n ∈ Finset.range (m + 1), (m.choose n : Padic (Arithmetic.residueChar w.1)) • x ^ n := by
    rw [add_comm, add_pow]
    simp only [one_pow, mul_one, Algebra.smul_def, map_natCast]
    apply Finset.sum_congr rfl
    intro n hn
    exact mul_comm _ _
  simp_rw [binomialTerm_eq]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, ← hb]
  simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.zero_lt_succ, ite_true]
  exact (smul_sub _ _ _).symm

theorem tsum_binomialTerm (ρ : Radius) (x : Completed D w ρ) (m : ℕ) :
    (∑' n : ℕ, binomialTerm D w ρ x m n) =
      (m : Padic (Arithmetic.residueChar w.1))⁻¹ • ((1 + x) ^ m - 1) :=
  (tsum_eq_sum (binomialTerm_zero_outside D w ρ x m)).trans (sum_binomialTerm D w ρ x m)

theorem norm_binomialTerm_le (ρ : Radius) (s : ℕ)
    (hs : ∀ n : ℕ, n ≠ 0 →
      ‖completedPadicMap D w ρ (n : Padic (Arithmetic.residueChar w.1))⁻¹‖ ≤ (n : ℝ) ^ s)
    (x : Completed D w ρ) (k n : ℕ) :
    ‖binomialTerm D w ρ x (Arithmetic.residueChar w.1 ^ k) n‖ ≤ (n : ℝ) ^ s * ‖x‖ ^ n := by
  by_cases hn : n = 0
  · simp only [hn, binomialTerm, PadicBinomialLogCoefficients.coefficient, ite_true,
      zero_smul, norm_zero]
    positivity
  · rw [binomialTerm, norm_padic_smul]
    exact mul_le_mul ((InitialThetaWittIwasawaLimit.norm_coefficient_le D w ρ _ n
      (pow_ne_zero k (Arithmetic.residueChar_prime w.1).ne_zero) hn).trans (hs n hn))
      (norm_pow_le _ _) (norm_nonneg _) (pow_nonneg (Nat.cast_nonneg n) s)

theorem tendsto_binomialTerm (ρ : Radius) (x : Completed D w ρ) (n : ℕ) :
    Filter.Tendsto (fun k : ℕ => binomialTerm D w ρ x (Arithmetic.residueChar w.1 ^ k) n)
      Filter.atTop (𝓝 (term D w ρ x n)) := by
  have h := (PadicBinomialLogCoefficients.tendsto_coefficient (Arithmetic.residueChar w.1) n).smul_const
    (x ^ n)
  simpa only [binomialTerm, term, logCoefficient] using h

theorem tendsto_quotient (ρ : Radius) (x : Completed D w ρ) (hx : ‖x‖ < 1) :
    Filter.Tendsto (quotient D w ρ x) Filter.atTop (𝓝 (logOneAdd D w ρ x)) := by
  obtain ⟨s, hs⟩ := exists_polynomial_bound D w ρ
  have hb : Summable (fun n : ℕ => (n : ℝ) ^ s * ‖x‖ ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one s (by simpa only [norm_norm] using hx)
  have h := tendsto_tsum_of_dominated_convergence hb (tendsto_binomialTerm D w ρ x)
    (Filter.Eventually.of_forall (fun k => norm_binomialTerm_le D w ρ s hs x k))
  have he (k : ℕ) : quotient D w ρ x k =
      ∑' n : ℕ, binomialTerm D w ρ x (Arithmetic.residueChar w.1 ^ k) n := by
    rw [tsum_binomialTerm, quotient, Nat.cast_pow]
  simpa only [← he, logOneAdd] using h

end
end JoshiTeich.Act1Scene1.InitialThetaWittRhoLogarithm
