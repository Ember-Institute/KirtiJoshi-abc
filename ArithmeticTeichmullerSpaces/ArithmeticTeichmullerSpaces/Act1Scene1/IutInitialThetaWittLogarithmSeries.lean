import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittLogDenominatorBounds
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAllRadiusSeries

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-LOGARITHM-SERIES
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, the
convergent logarithm used for the multiplicative-formal-group Tate period.
fidelity: defines the actual standard log(1+x) series in the existing
common complete ring. The proved polynomial denominator bound and
geometric decay give summability whenever every coordinate norm of x
is less than one. Coordinate evaluations and the actual Frobenius
preserve the resulting logarithm. Original proofs; no reference code copied.
boundary: Scene1/Derived; actual Tate coordinates must still be proved
to lie in this domain. Logarithmic power identities, eigenspace and
paper B/period/BK identities remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittLogarithmSeries

open JoshiTeich.Prologue
open InitialThetaWittAllRadiusPadicScalars InitialThetaWittPadicScalarNorm
open InitialThetaWittPadicScalarContinuity InitialThetaWittLogDenominatorBounds
open InitialThetaWittAllRadiusSeries
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def logCoefficient (n : ℕ) : Padic (Arithmetic.residueChar w.1) :=
  if n = 0 then 0 else (-1) ^ (n + 1) * (n : Padic (Arithmetic.residueChar w.1))⁻¹

def logTerm (x : Carrier D w) (n : ℕ) : Carrier D w := logCoefficient D w n • x ^ n

theorem norm_logCoefficient_le (ρ : Radius) (k : ℕ)
    (hk : ∀ n : ℕ, n ≠ 0 →
      ‖completedPadicMap D w ρ (n : Padic (Arithmetic.residueChar w.1))⁻¹‖ ≤ (n : ℝ) ^ k)
    (n : ℕ) : ‖completedPadicMap D w ρ (logCoefficient D w n)‖ ≤ (n : ℝ) ^ k := by
  by_cases hn : n = 0
  · simp only [logCoefficient, if_pos hn, map_zero, norm_zero]
    exact pow_nonneg (Nat.cast_nonneg n) k
  · rw [logCoefficient, if_neg hn, norm_completedPadicMap_mul_scalar]
    simp only [neg_one_pow_eq_ite]
    split_ifs <;> simpa only [map_neg, map_one, norm_neg, norm_one, one_mul] using hk n hn

theorem evaluate_logTerm (ρ : Radius) (x : Carrier D w) (n : ℕ) :
    InitialThetaWittAllRadiusCompletion.evaluate D w ρ (logTerm D w x n) =
      logCoefficient D w n • (InitialThetaWittAllRadiusCompletion.evaluate D w ρ x) ^ n := by
  rw [logTerm, evaluate_smul, map_pow]

theorem norm_evaluate_logTerm_le (ρ : Radius) (k : ℕ)
    (hk : ∀ n : ℕ, n ≠ 0 →
      ‖completedPadicMap D w ρ (n : Padic (Arithmetic.residueChar w.1))⁻¹‖ ≤ (n : ℝ) ^ k)
    (x : Carrier D w) (n : ℕ) :
    ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ (logTerm D w x n)‖ ≤
      (n : ℝ) ^ k * ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ x‖ ^ n := by
  rw [evaluate_logTerm, norm_padic_smul]
  exact mul_le_mul (norm_logCoefficient_le D w ρ k hk n) (norm_pow_le _ _)
    (norm_nonneg _) (pow_nonneg (Nat.cast_nonneg n) k)

theorem summable_logTerm (x : Carrier D w)
    (hx : ∀ ρ : Radius, InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ x < 1) :
    Summable (logTerm D w x) := by
  apply (summable_nat_iff_coordinates_tendsto_zero D w _).mpr
  intro ρ
  rw [tendsto_zero_iff_norm_tendsto_zero]
  obtain ⟨k, hk⟩ := exists_polynomial_bound D w ρ
  exact squeeze_zero (fun n => norm_nonneg _)
    (norm_evaluate_logTerm_le D w ρ k hk x)
    (tendsto_pow_const_mul_const_pow_of_lt_one k (norm_nonneg _) (hx ρ))

def logOneAdd (x : Carrier D w) : Carrier D w := ∑' n : ℕ, logTerm D w x n

theorem hasSum_logOneAdd (x : Carrier D w)
    (hx : ∀ ρ : Radius, InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ x < 1) :
    HasSum (logTerm D w x) (logOneAdd D w x) := (summable_logTerm D w x hx).hasSum

theorem evaluate_logOneAdd (ρ : Radius) (x : Carrier D w)
    (hx : ∀ r : Radius, InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w r x < 1) :
    InitialThetaWittAllRadiusCompletion.evaluate D w ρ (logOneAdd D w x) =
      ∑' n : ℕ, logCoefficient D w n • (InitialThetaWittAllRadiusCompletion.evaluate D w ρ x) ^ n := by
  exact (evaluate_tsum D w _ (summable_logTerm D w x hx) ρ).trans
    (tsum_congr (evaluate_logTerm D w ρ x))

theorem frobenius_logTerm (x : Carrier D w) (n : ℕ) :
    InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (logTerm D w x n) =
      logTerm D w (InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w x) n := by
  simp only [logTerm, InitialThetaWittAllRadiusPadicScalars.frobenius_smul, map_pow]

theorem frobenius_logOneAdd (x : Carrier D w)
    (hx : ∀ ρ : Radius, InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ x < 1) :
    InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (logOneAdd D w x) =
      logOneAdd D w (InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w x) := by
  exact (frobenius_tsum D w _ (summable_logTerm D w x hx)).trans
    (tsum_congr (frobenius_logTerm D w x))

theorem logOneAdd_zero : logOneAdd D w 0 = 0 := by
  have ht (n : ℕ) : logTerm D w 0 n = 0 := by
    cases n <;> simp [logTerm, logCoefficient]
  simp only [logOneAdd, ht, tsum_zero]

end
end JoshiTeich.Act1Scene1.InitialThetaWittLogarithmSeries
