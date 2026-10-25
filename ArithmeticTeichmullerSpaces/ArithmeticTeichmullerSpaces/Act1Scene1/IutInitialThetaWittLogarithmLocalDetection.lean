import ArithmeticTeichmullerSpaces.Act1Scene1.UltrametricLogTailBounds
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittLogarithmSeries

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-LOGARITHM-LOCAL-DETECTION
source: Joshi II logarithmic Tate periods in the rho-normed period ring.
fidelity: at every actual radius, constructs a positive neighborhood
on which the norm of log(1+x)-x is at most half the norm of x. Uses
the proved actual coefficient bound and ultrametric finite-sum estimates.
Consequently a zero log value in this neighborhood forces that same
coordinate of x to vanish. Original proofs; no reference code copied.
boundary: Scene1/Derived; this local detection lemma alone is not
global injectivity or a paper period-ring/BK identification.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittLogarithmLocalDetection

open JoshiTeich.Prologue
open InitialThetaWittAllRadiusPadicScalars InitialThetaWittLogarithmSeries
open InitialThetaWittLogDenominatorBounds InitialThetaWittAllRadiusSeries
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem logTerm_zero (x : Carrier D w) : logTerm D w x 0 = 0 := by
  simp [logTerm, logCoefficient]

theorem logTerm_one (x : Carrier D w) : logTerm D w x 1 = x := by
  simp [logTerm, logCoefficient]

theorem tail_hasSum (ρ : Radius) (x : Carrier D w)
    (hx : ∀ r : Radius, InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w r x < 1) :
    HasSum (fun n : ℕ => InitialThetaWittAllRadiusCompletion.evaluate D w ρ (logTerm D w x (n + 2)))
      (InitialThetaWittAllRadiusCompletion.evaluate D w ρ (logOneAdd D w x) -
        InitialThetaWittAllRadiusCompletion.evaluate D w ρ x) := by
  have h := (hasSum_iff_coordinates D w _ _).mp (hasSum_logOneAdd D w x hx) ρ
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, logTerm_zero, logTerm_one,
    map_zero] using (hasSum_nat_add_iff' 2).mpr h

theorem exists_local_detection (ρ : Radius) : ∃ δ : ℝ, 0 < δ ∧
    ∀ x : Carrier D w,
      (∀ r : Radius, InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w r x < 1) →
      ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ x‖ ≤ δ →
      ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ (logOneAdd D w x) -
        InitialThetaWittAllRadiusCompletion.evaluate D w ρ x‖ ≤
          ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ x‖ / 2 := by
  obtain ⟨k, hk⟩ := exists_polynomial_bound D w ρ
  refine ⟨(1 / 2 : ℝ) / (2 : ℝ) ^ k, by positivity, ?_⟩
  intro x hx hsmall
  have hs : (2 : ℝ) ^ k * ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ x‖ ≤ 1 / 2 := by
    simpa only [mul_comm] using
      (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ k)).mp hsmall
  have htail := tail_hasSum D w ρ x hx
  rw [← htail.tsum_eq]
  apply UltrametricLogTailBounds.norm_tsum_le_of_forall_le _ htail.summable _ (by positivity)
  intro n
  apply (norm_evaluate_logTerm_le D w ρ k hk x (n + 2)).trans
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    (UltrametricLogTailBounds.polynomial_geometric_tail_le k n _ (norm_nonneg _) hs)

theorem exists_zero_detection (ρ : Radius) : ∃ δ : ℝ, 0 < δ ∧
    ∀ x : Carrier D w,
      (∀ r : Radius, InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w r x < 1) →
      ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ x‖ ≤ δ →
      logOneAdd D w x = 0 → InitialThetaWittAllRadiusCompletion.evaluate D w ρ x = 0 := by
  obtain ⟨δ, hδ, h⟩ := exists_local_detection D w ρ
  refine ⟨δ, hδ, fun x hx hs hz => ?_⟩
  have he := h x hx hs
  rw [hz, map_zero, zero_sub, norm_neg] at he
  apply norm_eq_zero.mp
  linarith [norm_nonneg (InitialThetaWittAllRadiusCompletion.evaluate D w ρ x)]

end
end JoshiTeich.Act1Scene1.InitialThetaWittLogarithmLocalDetection
