import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittEigenEvaluationSurjective

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-UNTILT-LOG-DETECTION
source: Joshi II `pr:teichmuller-lift-A`, the kernel of logarithmic
evaluation in the displayed period sequence.
fidelity: the proved actual coefficient bounds and contracting logarithm
remainder give a positive ball in the original untilt on which a zero log
series forces a zero coordinate. Actual p-power tilt coordinates tend to
zero after theta evaluation. Hence a principal-unit period with zero theta
value has some p-power with sharp value one.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; this detects the kernel on actual principal-unit
periods. The whole phi=p period space is not assumed to be their image.
No discrete valuation or log-kernel law is input. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittUntiltLogDetection

open JoshiTeich.Prologue InitialThetaWittThetaBound InitialThetaWittThetaEvaluation
open InitialThetaWittPrincipalUnitDomain InitialThetaWittPrincipalUnitPeriod
open InitialThetaWittPrincipalUnitInjective InitialThetaWittLogarithmSeries
open InitialThetaWittEigenEvaluationSurjective
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem exists_untilt_zero_detection : ∃ R : ℝ, 0 < R ∧
    ∀ a : Untilt D w, ‖a‖ ≤ R →
      HasSum (fun n : ℕ => logCoefficient D w n • a ^ n) 0 → a = 0 := by
  obtain ⟨k, hk⟩ := exists_coefficient_bound D w
  have hp : 0 < (2 : ℝ) ^ k := by positivity
  have hp1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  let R : ℝ := (1 / 2) / (2 : ℝ) ^ k
  have hR : 0 < R := div_pos (by norm_num) hp
  have hR1 : R < 1 := (div_lt_iff₀ hp).mpr (by nlinarith)
  have hs : (2 : ℝ) ^ k * R ≤ 1 / 2 := by
    dsimp only [R]
    exact (mul_div_cancel₀ (1 / 2 : ℝ) hp.ne').le
  refine ⟨R, hR, fun a ha hzero => ?_⟩
  have hsum := UltrametricPowerSeriesLocalSurjectivity.hasSum_linear_add_remainder
    (untiltLogCoefficient D w) k hk (untiltLogCoefficient_zero D w)
      (untiltLogCoefficient_one D w) a (ha.trans_lt hR1)
  have he : a + UltrametricPowerSeriesContraction.remainder (untiltLogCoefficient D w) a = 0 :=
    hsum.unique (by simpa only [untiltLogCoefficient_mul] using hzero)
  have hnorm : ‖a‖ ≤ (1 / 2 : ℝ) * ‖a‖ := by
    calc
      ‖a‖ = ‖UltrametricPowerSeriesContraction.remainder (untiltLogCoefficient D w) a‖ := by
        exact (congrArg norm (eq_neg_of_add_eq_zero_left he)).trans (norm_neg _)
      _ ≤ _ := UltrametricPowerSeriesContraction.norm_remainder_le
        (untiltLogCoefficient D w) k hk hR hR1 hs ha
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg a]

theorem tendsto_untiltCoordinate_prime_pow (u : Principal D w) :
    Filter.Tendsto (fun k : ℕ => untiltCoordinate D w (u ^ (Arithmetic.residueChar w.1 ^ k)))
      Filter.atTop (𝓝 0) := by
  have h := ((evaluation_continuous D w).tendsto 0).comp (tendsto_coordinate_prime_pow D w u)
  simpa only [Function.comp_def, evaluation_coordinate, map_zero] using h

theorem exists_prime_pow_untiltCoordinate_eq_zero (u : Principal D w)
    (hu : evaluation D w (periodLog D w u) = 0) :
    ∃ k : ℕ, untiltCoordinate D w (u ^ (Arithmetic.residueChar w.1 ^ k)) = 0 := by
  obtain ⟨R, hR, hdetect⟩ := exists_untilt_zero_detection D w
  have hn : Filter.Tendsto (fun k : ℕ =>
      ‖untiltCoordinate D w (u ^ (Arithmetic.residueChar w.1 ^ k))‖) Filter.atTop (𝓝 0) := by
    simpa only [norm_zero] using (tendsto_untiltCoordinate_prime_pow D w u).norm
  obtain ⟨k, hk⟩ := (hn.eventually (gt_mem_nhds hR)).exists
  refine ⟨k, hdetect _ hk.le ?_⟩
  have hz : evaluation D w (periodLog D w (u ^ (Arithmetic.residueChar w.1 ^ k))) = 0 := by
    rw [periodLog_pow, map_nsmul, hu, nsmul_zero]
  have hsum := hasSum_evaluation_periodLog D w (u ^ (Arithmetic.residueChar w.1 ^ k))
  rwa [hz] at hsum

end
end JoshiTeich.Act1Scene1.InitialThetaWittUntiltLogDetection
