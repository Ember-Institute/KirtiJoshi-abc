import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittExponentialContraction
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittLogExpInverse
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.LinearCombination

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-EXPONENTIAL-LOCAL-INVERSE
source: Joshi II `pr:teichmuller-lift-A`, multiplicative-formal-group
periods; Banach's fixed point theorem applied to the actual remainder.
fidelity: exp(x)-1 maps the original closed rho^2/2 ball bijectively
onto itself. Its actual inverse is the already convergent log(1+y)
series. Constructs preimages and proves exp(log(1+y))=1+y rather than
assuming any local inverse, discreteness or field structure.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; this is a local result in each existing rho
completion. Teichmuller recognition and full period representation are
not input or asserted. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittExponentialLocalInverse

open JoshiTeich.Prologue InitialThetaWittAllRadiusPadicScalars
open InitialThetaWittExponentialSeries InitialThetaWittExponentialContraction
open InitialThetaWittLogExpInverse
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

theorem exists_exponential_preimage (ρ : Radius) (y : Ring D w ρ) (hy : ‖y‖ ≤ smallRadius ρ) :
    ∃ x : Ring D w ρ, ‖x‖ ≤ smallRadius ρ ∧ exp D w ρ x = 1 + y := by
  let T : Ring D w ρ → Ring D w ρ := fun x => y - remainder D w ρ x
  have hT : Set.MapsTo T (Metric.closedBall 0 (smallRadius ρ)) (Metric.closedBall 0 (smallRadius ρ)) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    calc
      ‖y - remainder D w ρ x‖ ≤ max ‖y‖ ‖remainder D w ρ x‖ := by
        simpa only [sub_eq_add_neg, norm_neg] using
          InitialThetaWittRhoUltrametric.norm_add_le_max D w ρ y (-remainder D w ρ x)
      _ ≤ smallRadius ρ := max_le hy
        ((norm_remainder_le D w ρ x hx).trans (by nlinarith [norm_nonneg x]))
  have hcontract : ContractingWith (1 / 2 : NNReal) (hT.restrict T _ _) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    have ha : ‖(a : Ring D w ρ)‖ ≤ smallRadius ρ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using a.property
    have hb : ‖(b : Ring D w ρ)‖ ≤ smallRadius ρ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using b.property
    change ‖(y - remainder D w ρ (a : Ring D w ρ)) - (y - remainder D w ρ (b : Ring D w ρ))‖ ≤
      (1 / 2 : ℝ) * ‖(a : Ring D w ρ) - (b : Ring D w ρ)‖
    rw [sub_sub_sub_cancel_left, norm_sub_rev]
    exact norm_remainder_sub_le D w ρ _ _ ha hb
  obtain ⟨x, hx, hfix, -, -⟩ := ContractingWith.exists_fixedPoint'
    Metric.isClosed_closedBall.isComplete hT hcontract (x := 0)
    (Metric.mem_closedBall_self (smallRadius_pos ρ).le) (edist_ne_top _ _)
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  refine ⟨x, hx, ?_⟩
  have he : y - remainder D w ρ x = x := hfix
  dsimp only [remainder] at he
  linear_combination -he

theorem logOneAdd_eq_preimage (ρ : Radius) (y x : Ring D w ρ)
    (hx : ‖x‖ ≤ smallRadius ρ) (he : exp D w ρ x = 1 + y) :
    InitialThetaWittRhoLogarithm.logOneAdd D w ρ y = x := by
  have h := log_exp D w ρ x (hx.trans_lt (smallRadius_lt_radius ρ))
  have hy : exp D w ρ x - 1 = y := by rw [he]; ring
  rw [hy] at h
  exact h

theorem exp_logOneAdd (ρ : Radius) (y : Ring D w ρ) (hy : ‖y‖ ≤ smallRadius ρ) :
    exp D w ρ (InitialThetaWittRhoLogarithm.logOneAdd D w ρ y) = 1 + y := by
  obtain ⟨x, hx, he⟩ := exists_exponential_preimage D w ρ y hy
  rw [logOneAdd_eq_preimage D w ρ y x hx he]
  exact he

theorem norm_logOneAdd_le (ρ : Radius) (y : Ring D w ρ) (hy : ‖y‖ ≤ smallRadius ρ) :
    ‖InitialThetaWittRhoLogarithm.logOneAdd D w ρ y‖ ≤ smallRadius ρ := by
  obtain ⟨x, hx, he⟩ := exists_exponential_preimage D w ρ y hy
  rw [logOneAdd_eq_preimage D w ρ y x hx he]
  exact hx

theorem exp_logOneAdd_sub_one (ρ : Radius) (y : Ring D w ρ) (hy : ‖y - 1‖ ≤ smallRadius ρ) :
    exp D w ρ (InitialThetaWittRhoLogarithm.logOneAdd D w ρ (y - 1)) = y := by
  rw [exp_logOneAdd D w ρ (y - 1) hy]
  ring

theorem existsUnique_exponential_preimage (ρ : Radius) (y : Ring D w ρ) (hy : ‖y‖ ≤ smallRadius ρ) :
    ∃! x : Ring D w ρ, ‖x‖ ≤ smallRadius ρ ∧ exp D w ρ x = 1 + y := by
  obtain ⟨x, hx, he⟩ := exists_exponential_preimage D w ρ y hy
  refine ⟨x, ⟨hx, he⟩, ?_⟩
  intro z hz
  exact (exp_eq_exp_iff D w ρ z x (hz.1.trans_lt (smallRadius_lt_radius ρ))
    (hx.trans_lt (smallRadius_lt_radius ρ))).mp (hz.2.trans he.symm)

end
end JoshiTeich.Act1Scene1.InitialThetaWittExponentialLocalInverse
