import ArithmeticTeichmullerSpaces.Act1Scene1.PadicBinomialLogCoefficients
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTateLogarithm
import Mathlib.Analysis.Normed.Group.Tannery

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-IWASAWA-LIMIT
source: Joshi II multiplicative Tate logarithm; Iwasawa normalized
p-power difference quotients and the rho-normed period algebra.
fidelity: expands each actual difference quotient as a finite binomial
series. Proves one polynomial-times-geometric norm bound independent
of the p-power exponent. Dominated convergence identifies the limit
with the already constructed common-ring logarithm.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; paper B/period/BK identities and Tate-log
nonvanishing remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittIwasawaLimit

open JoshiTeich.Prologue
open InitialThetaWittAllRadiusPadicScalars InitialThetaWittPadicScalarNorm
open InitialThetaWittPadicScalarContinuity InitialThetaWittLogDenominatorBounds
open InitialThetaWittLogarithmSeries InitialThetaWittAllRadiusSeries
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def binomialTerm (x : Carrier D w) (m n : ℕ) : Carrier D w :=
  PadicBinomialLogCoefficients.coefficient (Padic (Arithmetic.residueChar w.1)) m n • x ^ n

def quotient (x : Carrier D w) (k : ℕ) : Carrier D w :=
  ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k)⁻¹ •
    ((1 + x) ^ (Arithmetic.residueChar w.1 ^ k) - 1)

theorem binomialTerm_zero_outside (x : Carrier D w) (m n : ℕ) (hn : n ∉ Finset.range (m + 1)) :
    binomialTerm D w x m n = 0 := by
  have hmn : m < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self m) (Nat.le_of_not_gt (by simpa using hn))
  simp only [binomialTerm, PadicBinomialLogCoefficients.coefficient, Nat.choose_eq_zero_of_lt hmn,
    Nat.cast_zero, zero_div, ite_self, zero_smul]

theorem summable_binomialTerm (x : Carrier D w) (m : ℕ) : Summable (binomialTerm D w x m) :=
  summable_of_ne_finset_zero (binomialTerm_zero_outside D w x m)

theorem binomialTerm_eq (x : Carrier D w) (m n : ℕ) :
    binomialTerm D w x m n =
      (m : Padic (Arithmetic.residueChar w.1))⁻¹ •
        ((m.choose n : Padic (Arithmetic.residueChar w.1)) • x ^ n) -
      if n = 0 then (m : Padic (Arithmetic.residueChar w.1))⁻¹ • (1 : Carrier D w) else 0 := by
  by_cases hn : n = 0
  · simp [binomialTerm, PadicBinomialLogCoefficients.coefficient, hn]
  · simp only [binomialTerm, PadicBinomialLogCoefficients.coefficient, if_neg hn,
      sub_zero, div_eq_mul_inv, smul_smul]
    rw [mul_comm]

theorem sum_binomialTerm (x : Carrier D w) (m : ℕ) :
    (∑ n ∈ Finset.range (m + 1), binomialTerm D w x m n) =
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

theorem tsum_binomialTerm (x : Carrier D w) (m : ℕ) :
    (∑' n : ℕ, binomialTerm D w x m n) =
      (m : Padic (Arithmetic.residueChar w.1))⁻¹ • ((1 + x) ^ m - 1) :=
  (tsum_eq_sum (binomialTerm_zero_outside D w x m)).trans (sum_binomialTerm D w x m)

theorem norm_coefficient_le (ρ : Radius) (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    ‖completedPadicMap D w ρ (PadicBinomialLogCoefficients.coefficient
      (Padic (Arithmetic.residueChar w.1)) m n)‖ ≤
      ‖completedPadicMap D w ρ (n : Padic (Arithmetic.residueChar w.1))⁻¹‖ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [PadicBinomialLogCoefficients.coefficient_succ_eq _ m j hm, div_eq_mul_inv,
    norm_completedPadicMap_mul_scalar, map_natCast]
  apply mul_le_of_le_one_left (norm_nonneg _)
  simpa only [map_natCast] using norm_completedPadicInt_le_one D w ρ
    ((m - 1).choose j : PadicInt (Arithmetic.residueChar w.1))

theorem norm_evaluate_binomialTerm_le (ρ : Radius) (s : ℕ)
    (hs : ∀ n : ℕ, n ≠ 0 →
      ‖completedPadicMap D w ρ (n : Padic (Arithmetic.residueChar w.1))⁻¹‖ ≤ (n : ℝ) ^ s)
    (x : Carrier D w) (k n : ℕ) :
    ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ
      (binomialTerm D w x (Arithmetic.residueChar w.1 ^ k) n)‖ ≤
      (n : ℝ) ^ s * ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ x‖ ^ n := by
  by_cases hn : n = 0
  · simp only [hn, binomialTerm, PadicBinomialLogCoefficients.coefficient, ite_true,
      zero_smul, map_zero, norm_zero]
    positivity
  · rw [binomialTerm, evaluate_smul, map_pow, norm_padic_smul]
    exact mul_le_mul ((norm_coefficient_le D w ρ _ n
      (pow_ne_zero k (Arithmetic.residueChar_prime w.1).ne_zero) hn).trans (hs n hn))
      (norm_pow_le _ _) (norm_nonneg _) (pow_nonneg (Nat.cast_nonneg n) s)

theorem tendsto_evaluate_binomialTerm (ρ : Radius) (x : Carrier D w) (n : ℕ) :
    Filter.Tendsto (fun k : ℕ => InitialThetaWittAllRadiusCompletion.evaluate D w ρ
      (binomialTerm D w x (Arithmetic.residueChar w.1 ^ k) n)) Filter.atTop
      (𝓝 (InitialThetaWittAllRadiusCompletion.evaluate D w ρ (logTerm D w x n))) := by
  have h := (PadicBinomialLogCoefficients.tendsto_coefficient (Arithmetic.residueChar w.1) n).smul_const
    ((InitialThetaWittAllRadiusCompletion.evaluate D w ρ x) ^ n)
  simpa only [binomialTerm, evaluate_smul, map_pow, evaluate_logTerm, logCoefficient] using h

theorem tendsto_quotient (x : Carrier D w)
    (hx : ∀ ρ : Radius, InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ x < 1) :
    Filter.Tendsto (quotient D w x) Filter.atTop (𝓝 (logOneAdd D w x)) := by
  apply (InitialThetaWittAllRadiusCompletion.tendsto_iff_coordinates D w _ _ _).mpr
  intro ρ
  obtain ⟨s, hs⟩ := exists_polynomial_bound D w ρ
  have hr := hx ρ
  change ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ x‖ < 1 at hr
  have hb : Summable (fun n : ℕ => (n : ℝ) ^ s *
      ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ x‖ ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one s (by simpa only [norm_norm] using hr)
  have h := tendsto_tsum_of_dominated_convergence hb
    (tendsto_evaluate_binomialTerm D w ρ x)
    (Filter.Eventually.of_forall (fun k => norm_evaluate_binomialTerm_le D w ρ s hs x k))
  have he (k : ℕ) : InitialThetaWittAllRadiusCompletion.evaluate D w ρ (quotient D w x k) =
      ∑' n : ℕ, InitialThetaWittAllRadiusCompletion.evaluate D w ρ
        (binomialTerm D w x (Arithmetic.residueChar w.1 ^ k) n) := by
    rw [← evaluate_tsum D w _ (summable_binomialTerm D w x _) ρ, tsum_binomialTerm]
    simp only [quotient, Nat.cast_pow]
  have hl := evaluate_tsum D w _ (summable_logTerm D w x hx) ρ
  simpa only [← he, ← hl, logOneAdd] using h

end
end JoshiTeich.Act1Scene1.InitialThetaWittIwasawaLimit
