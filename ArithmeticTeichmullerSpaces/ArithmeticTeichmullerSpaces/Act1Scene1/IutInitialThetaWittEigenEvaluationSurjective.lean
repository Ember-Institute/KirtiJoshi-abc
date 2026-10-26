import ArithmeticTeichmullerSpaces.Act1Scene1.UltrametricPowerSeriesLocalSurjectivity
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittPrincipalUnitLift

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-EIGEN-EVALUATION-SURJECTIVE
source: Joshi II `pr:teichmuller-lift-A`, its proof and the displayed
sequence T_y tensor Q_p -> B^{phi=p} -> K_y -> 0.
fidelity: obtains polynomial bounds for the actual untilt logarithm
coefficients from the proved period coefficient bounds and theta's
contraction. A fixed point gives a logarithm preimage on a positive
closed ball in the original untilt. The actual principal tilt lift
produces phi=p periods evaluating onto this ball. Q_p-linearity and
actual powers of p then prove surjectivity onto the entire untilt.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; the full kernel comparison and paper period
carrier identity remain open. No log-surjectivity, discrete valuation,
isometric scalar action or new comparison law is assumed. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittEigenEvaluationSurjective

open JoshiTeich.Prologue InitialThetaWittThetaBound
open InitialThetaWittLogarithmSeries InitialThetaWittThetaPadicCompatibility
open InitialThetaWittAllRadiusPadicScalars InitialThetaWittPrincipalUnitLift
open InitialThetaWittRationalTatePeriod
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def untiltLogCoefficient (n : ℕ) : Untilt D w := untiltPadicMap D w (logCoefficient D w n)

theorem untiltLogCoefficient_zero : untiltLogCoefficient D w 0 = 0 := by
  simp [untiltLogCoefficient, logCoefficient]

theorem untiltLogCoefficient_one : untiltLogCoefficient D w 1 = 1 := by
  simp [untiltLogCoefficient, logCoefficient]

theorem untiltLogCoefficient_mul (n : ℕ) (x : Untilt D w) :
    untiltLogCoefficient D w n * x = logCoefficient D w n • x := rfl

theorem exists_coefficient_bound :
    ∃ k : ℕ, ∀ n : ℕ, ‖untiltLogCoefficient D w n‖ ≤ (n : ℝ) ^ k := by
  obtain ⟨k, hk⟩ := InitialThetaWittLogDenominatorBounds.exists_polynomial_bound D w (radius D w)
  refine ⟨k, fun n => ?_⟩
  have he := InitialThetaWittThetaEvaluation.evaluation_norm_le D w
    (commonPadicMap D w (logCoefficient D w n))
  rw [evaluation_commonPadicMap] at he
  apply he.trans
  change ‖InitialThetaWittAllRadiusCompletion.evaluate D w (radius D w)
    (commonPadicMap D w (logCoefficient D w n))‖ ≤ _
  rw [evaluate_padic]
  exact norm_logCoefficient_le D w (radius D w) k hk n

theorem exists_local_preimage :
    ∃ R : ℝ, 0 < R ∧ ∀ y : Untilt D w, ‖y‖ ≤ R →
      ∃ x : InitialThetaWittAdditiveTatePeriod.frobeniusPrimeSubmodule D w,
        eigenEvaluation D w x = y := by
  obtain ⟨k, hk⟩ := exists_coefficient_bound D w
  obtain ⟨R, hR, hR1, hlocal⟩ :=
    UltrametricPowerSeriesLocalSurjectivity.exists_local_surjectivity
      (untiltLogCoefficient D w) k hk (untiltLogCoefficient_zero D w) (untiltLogCoefficient_one D w)
  refine ⟨R, hR, fun y hy => ?_⟩
  obtain ⟨a, ha, hsum⟩ := hlocal y hy
  have hnear : ‖(1 + a) - 1‖ < 1 := by
    simpa only [add_sub_cancel_left] using ha.trans_lt hR1
  have hn : ‖1 + a‖ = 1 := UltrametricPrincipalUnits.norm_eq_one _ hnear
  have ha0 : 1 + a ≠ 0 := norm_pos_iff.mp (hn ▸ zero_lt_one)
  let z : UntilPrincipal D w := ⟨Units.mk0 (1 + a) ha0, hnear⟩
  refine ⟨liftPeriod D w z, ?_⟩
  have ht : HasSum (fun n : ℕ => logCoefficient D w n • a ^ n)
      (eigenEvaluation D w (liftPeriod D w z)) := by
    simpa only [z, Units.val_mk0, add_sub_cancel_left] using
      hasSum_eigenEvaluation_liftPeriod D w z
  exact ht.unique (by simpa only [untiltLogCoefficient_mul] using hsum)

theorem eigenEvaluation_surjective : Function.Surjective (eigenEvaluation D w) := by
  obtain ⟨R, hR, hlocal⟩ := exists_local_preimage D w
  intro y
  by_cases hy : y = 0
  · exact ⟨0, by simp [hy]⟩
  have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hR hy0)
    (InitialThetaCanonicalGeometricFontaine.primeNormFact D w).out.2
  let a : Padic (Arithmetic.residueChar w.1) :=
    (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ m
  have ha0 : a ≠ 0 := pow_ne_zero m
    (Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero)
  have hsmall : ‖a • y‖ ≤ R := by
    change ‖untiltPadicMap D w a * y‖ ≤ R
    dsimp only [a]
    rw [map_pow, map_natCast, norm_mul, norm_pow]
    exact ((lt_div_iff₀ hy0).mp hm).le
  obtain ⟨x, hx⟩ := hlocal (a • y) hsmall
  refine ⟨a⁻¹ • x, ?_⟩
  rw [map_smul, hx, inv_smul_smul₀ ha0]

end
end JoshiTeich.Act1Scene1.InitialThetaWittEigenEvaluationSurjective
