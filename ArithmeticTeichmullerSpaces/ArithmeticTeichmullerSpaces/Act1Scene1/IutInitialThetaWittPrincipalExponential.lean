import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittExponentialLocalInverse
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittPrincipalUnitInjective

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-PRINCIPAL-EXPONENTIAL
source: Joshi II `pr:teichmuller-lift-A` and the multiplicative-formal-group
description of the period source `eq:tate-module-of-lubin-tate`.
fidelity: the actual exponential of a sufficiently small original
principal-unit period recovers that same unit's Teichmuller coordinate.
Every principal unit reaches this domain after an actual p-power.
Also proves uniqueness of a small common-ring element with that
exponential coordinate, using the already faithful radius evaluation.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; no existence of a Teichmuller representative
for arbitrary full phi=p exponentials is assumed or asserted. Full
period representation and full kernel identity remain open. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittPrincipalExponential

open JoshiTeich.Prologue InitialThetaWittAllRadiusPadicScalars
open InitialThetaWittExponentialSeries InitialThetaWittExponentialContraction
open InitialThetaWittExponentialLocalInverse InitialThetaWittLogExpInverse
open InitialThetaWittPrincipalUnitDomain InitialThetaWittPrincipalUnitPeriod
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem norm_evaluate_periodLog_le (ρ : Radius) (u : Principal D w)
    (hu : InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ (coordinate D w u) ≤ smallRadius ρ) :
    ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ (periodLog D w u)‖ ≤ smallRadius ρ := by
  rw [periodLog, InitialThetaWittRhoLogarithm.evaluate_logOneAdd D w ρ _ (coordinate_lt_one D w u)]
  exact norm_logOneAdd_le D w ρ _ hu

theorem exp_evaluate_periodLog (ρ : Radius) (u : Principal D w)
    (hu : InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ (coordinate D w u) ≤ smallRadius ρ) :
    exp D w ρ (InitialThetaWittAllRadiusCompletion.evaluate D w ρ (periodLog D w u)) =
      InitialThetaWittRhoExpansion.ainfMap D w ρ (wittUnit D w u) := by
  rw [periodLog, InitialThetaWittRhoLogarithm.evaluate_logOneAdd D w ρ _ (coordinate_lt_one D w u),
    exp_logOneAdd D w ρ _ hu]
  change 1 + InitialThetaWittRhoExpansion.ainfMap D w ρ (wittUnit D w u - 1) = _
  rw [map_sub, map_one]
  ring

theorem exists_prime_pow_exp_period (ρ : Radius) (u : Principal D w) : ∃ k : ℕ,
    InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ
        (coordinate D w (u ^ (Arithmetic.residueChar w.1 ^ k))) ≤ smallRadius ρ ∧
      exp D w ρ (InitialThetaWittAllRadiusCompletion.evaluate D w ρ
          (periodLog D w (u ^ (Arithmetic.residueChar w.1 ^ k)))) =
        InitialThetaWittRhoExpansion.ainfMap D w ρ (wittUnit D w (u ^ (Arithmetic.residueChar w.1 ^ k))) := by
  have h := (InitialThetaWittAllRadiusCompletion.tendsto_iff_coordinates D w _ _ _).mp
    (InitialThetaWittPrincipalUnitInjective.tendsto_coordinate_prime_pow D w u) ρ
  rw [map_zero] at h
  have hn := h.norm
  rw [norm_zero] at hn
  obtain ⟨k, hk⟩ := (hn.eventually (gt_mem_nhds (smallRadius_pos ρ))).exists
  exact ⟨k, hk.le, exp_evaluate_periodLog D w ρ _ hk.le⟩

theorem periodLog_eq_of_exp_teichmuller (ρ : Radius)
    (z : InitialThetaWittAllRadiusCompletion.Carrier D w)
    (hz : ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ z‖ < ρ.val.toReal)
    (u : Principal D w)
    (hu : InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ (coordinate D w u) ≤ smallRadius ρ)
    (he : exp D w ρ (InitialThetaWittAllRadiusCompletion.evaluate D w ρ z) =
      InitialThetaWittRhoExpansion.ainfMap D w ρ (wittUnit D w u)) : periodLog D w u = z := by
  apply InitialThetaWittRadiusFaithfulness.evaluate_injective D w ρ
  apply (exp_eq_exp_iff D w ρ _ _
    ((norm_evaluate_periodLog_le D w ρ u hu).trans_lt (smallRadius_lt_radius ρ)) hz).mp
  exact (exp_evaluate_periodLog D w ρ u hu).trans he.symm

end
end JoshiTeich.Act1Scene1.InitialThetaWittPrincipalExponential
